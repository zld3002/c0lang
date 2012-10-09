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
    (* the following represent error conditions not recognized by the test
       framework -- we only distinguish them in order to give a more
       informative error message if one occurs. *)
    | LinkError
    | RuntimeError
    | NoResultValue
    | UnexpectedExitStatus of Word8.word
    | UnexpectedSignal of Posix.Process.signal

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
     | RuntimeError => "Program exposed internal bug in coin"
     | NoResultValue => "Program could not write a result value"
     | UnexpectedExitStatus w => "Runtime error: coin_exec exited with status "
                               ^ Word8.fmt StringCvt.DEC w ^ " (linker failed?)"
     | UnexpectedSignal s => "Unexpected signal received: "
                            ^ SysWord.fmt StringCvt.DEC (Posix.Signal.toWord s)

  fun did_return NONE (Return _) = true
    | did_return (SOME w) (Return w') = w = w'
    | did_return _ _ = false

  fun did_segfault r = r = SIGSEGV
  fun did_div_by_zero r = r = SIGFPE
  fun did_abort r = r = SIGABRT
  fun did_infloop r = r = SIGALRM
  fun did_error r = r = CompileError

  (* XXX BAD: assume we're run from the c0 directory 
   * 
   * We should just force cc0 and cc0-test to be in the same
   * directory; we shouldn't specify the c0 directory for running
   * this.  - Rjs 08-12-2010
   *
   * Yes, but how to make sure cc0-test.cm continues to work?  -wjl
   * 08-20-2010 *)
  val coin_exec =
    let 
       val curdir = OS.FileSys.getDir ()
       val coin_exec_exe = OS.Path.concat (curdir, "bin/coin-exec.exe")
    in
      print ("Invoking " ^ coin_exec_exe ^ "\n");
      coin_exec_exe
    end

  val runtime = ref "bare"

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

  fun test files =
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
            P.exece (coin_exec, coin_exec :: files,
                     ["C0_RESULT_FILE=" ^ result_file])
            handle OS.SysErr _ => Posix.Process.exit 0wx5 (* impossible? *)
          end
        | SOME pid => P.waitpid (P.W_CHILD pid, [])
      val result = get_result result_file
      val () = FS.unlink result_file
    in
        case status of 
          P.W_EXITED =>
          (case result of
              NONE => UnexpectedExitStatus 0wx0 (* success is unexpected if
                                                   no result was written *)
            | SOME result => result)
        | P.W_EXITSTATUS 0wx1 => NoResultValue
        | P.W_EXITSTATUS 0wx2 => CompileError
        | P.W_EXITSTATUS 0wx3 => LinkError
        | P.W_EXITSTATUS 0wx4 => RuntimeError
        | P.W_EXITSTATUS w => 
          (case result of 
              SOME LinkError => LinkError (* may be impossible? *)
            | _ => UnexpectedExitStatus w)
        | P.W_SIGNALED s =>
          if      s = Posix.Signal.fpe  then SIGFPE
          else if s = Posix.Signal.alrm then SIGALRM
          else if s = Posix.Signal.segv then SIGSEGV
          else if s = Posix.Signal.abrt then SIGABRT
          else UnexpectedSignal s
        | P.W_STOPPED _ => raise Failed "Stopped"
    end

  val args_desc = "[-r runtime]"
  fun name () = "coin_" ^ (!runtime)

  fun set_name n = raise Failed "Coin cannot use a different runtime"

  datatype pred = LIB | TYPECHECK | GC | SAFE
  fun matches_pred SAFE = "unsafe" <> (!runtime)
    | matches_pred GC = "bare" <> (!runtime)
    | matches_pred _ = true
end)
