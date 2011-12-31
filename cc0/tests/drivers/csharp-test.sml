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
    | RuntimeError

  fun result_to_string (Return w) = "Program ran successfully with result "
                                  ^ Word32Signed.toString w
    | result_to_string SIGABRT = "Program aborted"
    | result_to_string SIGSEGV = "Program segfaulted"
    | result_to_string SIGFPE  = "Program divided by zero"
    | result_to_string SIGALRM = "Program timed out"
    | result_to_string CompileError = "Program failed to compile"
    | result_to_string RuntimeError = "Program failed to link"

  fun did_return NONE (Return _) = true
    | did_return (SOME w) (Return w') = w = w'
    | did_return _ _ = false

  fun did_segfault r = r = SIGSEGV
  fun did_div_by_zero r = r = SIGFPE
  fun did_abort r = r = SIGABRT
  fun did_infloop r = r = SIGALRM
  fun did_error r = r = CompileError

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
        | P.W_SIGNALED _ => 
          raise Failed ("Compiler exited with unexpected signal")
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
        val zval = if Word8Vector.length z > 0 then 
                      Word8Vector.sub (z,0)
                   else
                      0w0
    in
        (* This is the major difference between the regular test driver and
           the C# test driver. C# is managed code and doesn't die to Unix 
           signals the way the driver expects, so instead we catch exceptions
           within the C# program and write the appropriate value to the
           result file. Then this reads that value and tells the rest of the
           driver that the process died to the appropriate signal *)
        if Word8Vector.length z = 0 then
            SOME SIGSEGV
        (* Cases added to make this test driver compatible with C# code *)
        else if zval = 0w1 then
           SOME SIGSEGV
        else if zval = 0w2 then
           SOME SIGFPE
        else if zval = 0w3 then
           SOME SIGABRT
        else if zval = 0w4 then
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
            Posix.IO.dup2{old = devnull, new = FS.stdout};
            Posix.IO.dup2{old = devnull, new = FS.stderr};
            (* Set an alarm, prepare to die. *)
            ignore (Posix.Process.alarm (Time.fromSeconds 7));
            P.exece ("/usr/bin/mono", ["mono", program], ["C0_RESULT_FILE=" ^ result_file])
          end
        | SOME pid => P.waitpid (P.W_CHILD pid, [])

      val () = FS.unlink program
      val result = get_result result_file
      val () = FS.unlink result_file
    in
        case status of 
          P.W_EXITED => valOf result (* handled below *)
        | P.W_EXITSTATUS 0w1 => SIGFPE (* raise Failed "Program couldn't write result!" *)
        | P.W_EXITSTATUS w => valOf result (* handled below *)
        | P.W_SIGNALED s =>
          if      s = Posix.Signal.fpe  then SIGFPE
          else if s = Posix.Signal.alrm then SIGALRM
          else if s = Posix.Signal.segv then SIGSEGV
          else if s = Posix.Signal.abrt then SIGABRT
          else (print ("OH NOES!\nSig: ");
                print (SysWord.toString (Posix.Signal.toWord s) ^ "\n");
                raise Failed "Unexpected signal received")
        | P.W_STOPPED _ => raise Failed "Stopped"
    end
    handle Option => raise Failed "Couldn't read result -- abnormal termination?"

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
