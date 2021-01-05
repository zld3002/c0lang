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
    | CompileError
    | LinkError
    | EXIT_FAILURE
    | UnexpectedReturnValue of Word8.word
    | NoResultValue

  fun result_to_string result = 
     case result of 
       Return w => "Program ran successfully with result "
                                  ^ Word32Signed.toString w
     | SIGABRT => "Program aborted"
     | SIGSEGV => "Program segfaulted"
     | SIGFPE  => "Program divided by zero"
     | SIGALRM => "Program timed out"
     | CompileError => "Program failed to compile"
     | LinkError => "Program failed to link"
     | EXIT_FAILURE => "Program returned 1, presumably via error()" 
     | UnexpectedReturnValue w => 
       "Runtime error: returned " ^  Word8.toString w ^ " (linker failed?)"
     | NoResultValue => "Returned successfuly, but no result value was written"

  fun did_return NONE (Return _) = true
    | did_return (SOME w) (Return w') = w = w'
    | did_return _ _ = false

  fun did_segfault r = r = SIGSEGV
  fun did_div_by_zero r = r = SIGFPE
  fun did_abort r = r = SIGABRT
  fun did_infloop r = r = SIGALRM
  fun did_error r = r = CompileError
  fun did_failure r = r = EXIT_FAILURE

  (* XXX: assume we're run from the c0 directory *)
  val cc0 =
    let val curdir = OS.FileSys.getDir ()
    in
      (* XXX BAD - WE SHOULD JUST FORCE cc0 AND cc0-test TO BE IN 
       * THE SAME DIRECTORY, WE SHOULDN'T SPECIFY THE c0 DIRECTORY
       * FOR RUNNING THIS - Rjs August 12 *)
      (* Yes, but how to make sure cc0-test.cm continues to work?
         -wjl 08-20-2010 *)
      print ("The time is now " ^ OS.Path.concat (curdir, "bin/cc0") ^ "\n");
      OS.Path.concat (curdir, "bin/cc0")
    end

  val runtime = ref "c0rt"

  (* Timeouts for how long the compiler can run
   * and how long a test case can run, in seconds *)
  val COMPILER_TIMEOUT = 15
  val PROGRAM_TIMEOUT = 15

  fun compile files =
    let
      val compiler_args = "--verbose" :: "-r" :: (!runtime) :: "-n" :: files
      (* val () = 
      print ("Go: " ^ cc0 ^ " " ^ String.concatWith " " compiler_args ^ "\n")*)
      val (_, status) = 
        case P.fork () of
          NONE => 
          let val devnull = FS.openf ("/dev/null", FS.O_WRONLY, FS.O.append) in
            Posix.IO.dup2{old = devnull, new = FS.stdout};
            Posix.IO.dup2{old = devnull, new = FS.stderr};
            (* Some test cases cause some versions of GCC
             * to take an unreasonably long amount of time,
             * so we set a timeout *)
            ignore (Posix.Process.alarm (Time.fromSeconds COMPILER_TIMEOUT));
            P.execp (cc0, cc0 :: compiler_args)
            handle OS.SysErr _ => Posix.Process.exit 0w1
          end
        | SOME pid => P.waitpid (P.W_CHILD pid, [])
      in
        case status of 
          P.W_EXITED => true
        | P.W_EXITSTATUS 0w1 => false
        | P.W_EXITSTATUS w => 
          raise Failed ("Compiler exited with status " ^ Word8.toString w)
        | P.W_SIGNALED signal =>
            if signal = Posix.Signal.alrm
              then (
                print "Compiler timed out\n";
                false (* Indicate compilation failure. *)
              )
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
            SOME LinkError
        else if Word8Vector.length bytes < 4 then
            NONE
        else
            SOME (Return (Word32.fromLargeWord 
                              (PackWord32Little.subVec (bytes, 0))))
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

            Posix.IO.dup2{old = devnull, new = FS.stdout};
            Posix.IO.dup2{old = devnull, new = FS.stderr};
            (* Set an alarm, prepare to die. *)
            ignore (Posix.Process.alarm (Time.fromSeconds PROGRAM_TIMEOUT));
            P.exece ("./" ^ program, [], ["C0_RESULT_FILE=" ^ result_file])
          end
        | SOME pid => P.waitpid (P.W_CHILD pid, [])

      val () = FS.unlink program
      val result = get_result result_file
      val () = FS.unlink result_file
    in
        case status of 
          (* NB: a link error may manifest with either success or
             failure as its exit code (on Linux I think it's 0, on OS
             X it's otherwise), so the code here and above (function
             get_result) has to be robust in reporting link errors. If
             a linker error gives the exit status 1, then the harness
             will become confused.*)

          P.W_EXITED =>
          (case result of
              NONE => NoResultValue
            | SOME result => result)
        | P.W_EXITSTATUS 0wx1 => EXIT_FAILURE
        | P.W_EXITSTATUS w => 
          (case result of 
              SOME LinkError => LinkError
            | _ => UnexpectedReturnValue w)
        | P.W_SIGNALED s =>
          if      s = Posix.Signal.fpe  then SIGFPE
          else if s = Posix.Signal.alrm then SIGALRM
          else if s = Posix.Signal.segv then SIGSEGV
          else if s = Posix.Signal.kill then SIGSEGV
            (* This is a lie, but on Ubuntu 12.04 stack overflow
             * raises SIGKILL not SIGSEGV, which will trip up
             * the testing harness if we don't treat it like SEGV.
             *  - Rob Simmons Jan 13, 2013 *)
          else if s = Posix.Signal.bus then SIGSEGV
          else if s = Posix.Signal.abrt then SIGABRT
          else (print ("OH NOES!\nSig: ");
                print (SysWord.toString (Posix.Signal.toWord s) ^ "\n");
                raise Failed "Unexpected signal received")
        | P.W_STOPPED _ => raise Failed "Stopped"
    end

  fun test files = 
      if compile files
      then run "a.out"
      else CompileError

  val args_desc = "[-r runtime]"
  fun name () = "cc0_" ^ (!runtime)

  fun set_name n = runtime := n

  datatype pred = LIB | TYPECHECK | GC | SAFE
  fun matches_pred SAFE = "unsafe" <> (!runtime)
    | matches_pred GC = "bare" <> (!runtime)
    | matches_pred _ = true
end)
