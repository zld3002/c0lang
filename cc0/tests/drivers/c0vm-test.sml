structure Test = Testing (struct

  structure FS = Posix.FileSys
  structure P = Posix.Process

  exception Failed of string

  datatype result =
      Return of Word32.word
    | SIGABRT
    | SIGSEGV
    | SIGFPE
    | SIGALRM
    | EXIT_FAILURE
    | CompileError
    | CompileTimeout
    | RuntimeError

  fun result_to_string (Return w) = "Program ran successfully with result "
                                  ^ Word32Signed.toString w
    | result_to_string SIGABRT = "Program aborted"
    | result_to_string SIGSEGV = "Program segfaulted"
    | result_to_string SIGFPE  = "Program divided by zero"
    | result_to_string SIGALRM = "Program timed out"
    | result_to_string EXIT_FAILURE = "Program returned, signaling failure"
    | result_to_string CompileError = "Program failed to compile"
    | result_to_string CompileTimeout = "Compilation timed out"
    | result_to_string RuntimeError = "Program failed to link"

  fun did_return NONE (Return _) = true
    | did_return (SOME w) (Return w') = w = w'
    | did_return _ _ = false

  fun did_failure r = r = EXIT_FAILURE
  fun did_segfault r = r = SIGSEGV
  fun did_div_by_zero r = r = SIGFPE
  fun did_abort r = r = SIGABRT
  fun did_infloop r = r = SIGALRM
  fun did_error r = r = CompileError

  (* XXX: assume we're run from the c0 directory *)
  val (cc0, c0vm) =
    let val curdir = OS.FileSys.getDir ()
    in
      (* XXX BAD - WE SHOULD JUST FORCE cc0 AND cc0-test TO BE IN 
       * THE SAME DIRECTORY, WE SHOULDN'T SPECIFY THE c0 DIRECTORY
       * FOR RUNNING THIS - Rjs August 12 *)
      (* Yes, but how to make sure cc0-test.cm continues to work?
         -wjl 08-20-2010 *)
      print ("The time is now " ^ OS.Path.concat (curdir, "bin/cc0") ^ "\n");
      (OS.Path.concat (curdir, "bin/cc0"),
       OS.Path.concat (curdir, "vm/c0vm"))
    end

  datatype compile_result = OK | ERROR | TIMEOUT

  fun compile files =
    let
      val compiler_args = "--verbose" :: "-b" :: "-n" :: files
      val (_, status) = 
        case P.fork () of
          NONE => 
          let val devnull = FS.openf ("/dev/null", FS.O_WRONLY, FS.O.append) in
            Posix.IO.dup2{old = devnull, new = FS.stdout};
            Posix.IO.dup2{old = devnull, new = FS.stderr};
            (* XXX compiler is quadratic on some test cases so we set a timer.
               compiler timeout is distinguished as its own type of failure. *)
            ignore (Posix.Process.alarm (Time.fromSeconds 7));
            P.execp (cc0, compiler_args)
            handle OS.SysErr _ => Posix.Process.exit 0w1
          end
        | SOME pid => P.waitpid (P.W_CHILD pid, [])
      in
        case status of 
          P.W_EXITED => OK
        | P.W_EXITSTATUS 0w1 => ERROR
        | P.W_EXITSTATUS w => 
          raise Failed ("Compiler exited with status " ^ Word8.toString w)
        | P.W_SIGNALED s => 
          if s = Posix.Signal.alrm then TIMEOUT
          else raise Failed ("Compiler exited with unexpected signal")
        | P.W_STOPPED _ => 
          raise Failed ("Compiler stopped unexpectedly")
      end

  fun get_result filename =
    let val f = FS.createf (filename, FS.O_RDONLY, FS.O.nonblock,
                            FS.S.flags [FS.S.irusr, FS.S.iwusr,
                                        FS.S.irgrp, FS.S.iwgrp,
                                        FS.S.iroth, FS.S.iwoth])
        val z = Posix.IO.readVec (f, 1)
        val bytes = Posix.IO.readVec (f, 4)
        val () = Posix.IO.close f
    in
        if Word8Vector.length z = 0 then
            SOME RuntimeError
        else if Word8Vector.length bytes < 4 then
            NONE
        else
            SOME (Return (Word32.fromLargeWord (PackWord32Little.subVec (bytes, 0))))
    end
    (* Raising Failed aborts testing completely *)
    handle OS.SysErr _ => raise Failed "Problem reading result file!"

  fun run program =
    let
      val result_file = "._c0_result"
      val (_, status) = 
        case P.fork () of
          NONE => 
          let val devnull = FS.openf ("/dev/null", FS.O_WRONLY, FS.O.append) in
            (* XXX This is really not right, we should capture the integer
             * outputted (to stderr or stdout?) through a pipe or by 
             * redirecting it to a file and then read it in the parent process
             * to verify that it is, in fact, the integer that we expected. *)
            Posix.IO.dup2{old = devnull, new = FS.stdout};
            Posix.IO.dup2{old = devnull, new = FS.stderr};

            (* Set an alarm, prepare to die. *)
            ignore (Posix.Process.alarm (Time.fromSeconds 7));

            P.exece (c0vm, ["c0vm", program], ["C0_RESULT_FILE=" ^ result_file])
            (* XXX why doesn't this fire when c0vm doesn't exist? *)
            (*
            handle OS.SysErr _ => (print ("Couldn't execute C0VM binary" ^
                                          c0vm ^ "\n");
                                   raise Failed "no c0vm binary")
            *)
          end
        | SOME pid => P.waitpid (P.W_CHILD pid, [])

      val () = FS.unlink program
      val result = get_result result_file
      val () = FS.unlink result_file
    in
        case status of 
          P.W_EXITED => valOf result (* handled below *)
        | P.W_EXITSTATUS 0w1 => EXIT_FAILURE
        | P.W_EXITSTATUS w => valOf result (* handled below *)
        | P.W_SIGNALED s =>
          if      s = Posix.Signal.fpe  then SIGFPE
          else if s = Posix.Signal.alrm then SIGALRM
          else if s = Posix.Signal.segv then SIGSEGV
	  else if s = Posix.Signal.bus then SIGSEGV
          else if s = Posix.Signal.abrt then SIGABRT
	  else raise Failed ("Unexpected signal 0x" ^ SysWord.toString (Posix.Signal.toWord s))
		     (* 
          else (print ("OH NOES!\nSig: ");
                print (SysWord.toString (Posix.Signal.toWord s) ^ "\n");
                raise Failed "Unexpected signal received")
		      *)
        | P.W_STOPPED _ => raise Failed "Stopped"
    end
    handle Option => raise Failed "Couldn't read result -- abnormal termination?"

  (* XXX HAX: should use -o instead, if the compiler worked that way *)

  (* find the last .c0 file (first from end) and turn the .c0 into a .bc0 *)
  fun bc0_file_aux [] = raise Failed "Couldn't figure out .bc0 file name"
    | bc0_file_aux (f::fs) =
        case OS.Path.splitBaseExt f of
            {base, ext = SOME "c0"} =>
                OS.Path.joinBaseExt {base = base, ext = SOME "bc0"}
          | {base, ext = SOME "c1"} =>
                OS.Path.joinBaseExt {base = base, ext = SOME "bc1"}
          | _ => bc0_file_aux fs
  fun bc0_file fs = bc0_file_aux (List.rev fs)

  fun check_executable path =
    if OS.FileSys.access (path, [OS.FileSys.A_EXEC])
    then ()
    else raise Failed
        ("File " ^ path ^ " does not exist or is not executable")

  fun test files = (check_executable cc0; check_executable c0vm;
                    case compile files of
                        OK => run (bc0_file files)
                      | ERROR => CompileError
                      | TIMEOUT => CompileTimeout)
                   handle e as Failed s => (print ("Failed: " ^ s ^ "\n");
                                            raise e)

  (* NB: c0vm only supports bare for now *)
  val args_desc = ""
  fun name () = "cc0_c0vm"

  (* ??? can't change the name on this one ... *)
  fun set_name n = ()

  datatype pred = LIB | TYPECHECK | GC | SAFE
  fun matches_pred GC = false
    | matches_pred _ = true
end)
