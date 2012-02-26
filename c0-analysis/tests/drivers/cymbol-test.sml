structure Test = Testing (struct
                  
  exception Compile

  datatype pred = LIB | TYPECHECK | GC | SAFE
  fun matches_pred p = 
    case p of
      LIB => Call.native
    | TYPECHECK => true
    | GC => false
    | SAFE => true

  val args_desc = ""
  fun set_name _ = ()
  fun name () = "cymbol"

  val word8_32 : Word32.word -> Word8.word = Word8.fromLarge o Word32.toLarge
  val word32_8 : Word8.word -> Word32.word = Word32.fromLarge o Word8.toLarge

  fun to_wordlist word = 
      [ word8_32 (Word32.>> (word, 0wx18)),
        word8_32 (Word32.>> (word, 0wx10)),
        word8_32 (Word32.>> (word, 0wx8)),
        word8_32             word ]

  fun from_wordlist word = 
      Word32.orb (Word32.<< (word32_8 (Word8Vector.sub (word, 0)), 0wx18),
      Word32.orb (Word32.<< (word32_8 (Word8Vector.sub (word, 1)), 0wx10),
      Word32.orb (Word32.<< (word32_8 (Word8Vector.sub (word, 2)), 0wx8),
                             word32_8 (Word8Vector.sub (word, 3)))))

  fun run_test files : Word8.word list =
    let
      val filter = List.filter (not o String.isPrefix "-")
      val (anno, files) =
          case files of
            "-d" :: files => (true, filter files) 
          | _ => (false, filter files)
    in
      case (Parser.silence true; CNaught.run anno (files, 90000000)) of
        NONE => [ 0wx4 ]
      | SOME x => 0wx10 :: to_wordlist x 
    end handle Error.NullPointer => [ 0wx2 ]
             | Error.ArrayOutOfBounds _ => [ 0wx7 ]
             | Error.AssertionFailed _ => [ 0wx6 ]
             | Div => [ 0wx3 ]
             | Overflow => [ 0wx3 ]
             | Error.Compilation => [ 0wx1 ]
             | Error.Dynamic s => [ 0wx5 ]

  datatype result  
    = Return of Word32.word
    | SIGSEGV
    | SIGFPE
    | SIGALRM
    | CompileError
    | RuntimeError
    | AssertionFailed
    | ArrayOutOfBounds
    | BlewUp

  fun test files = 
    let val {infd, outfd} = Posix.IO.pipe () in
      case Posix.Process.fork () of
        NONE => (* RUN THE TEST *)
        let 
          val devnull = Posix.FileSys.openf ("/dev/null",
                                             Posix.FileSys.O_WRONLY, 
                                             Posix.FileSys.O.append) 
          val to_slice = Word8VectorSlice.full o Word8Vector.fromList
          val i = Posix.IO.writeVec (outfd, to_slice [ 0wx1 ])
          val j = Posix.IO.writeVec (outfd, to_slice (run_test files))
        in
          Posix.IO.dup2{old = devnull, new = Posix.FileSys.stdout};
          Posix.IO.dup2{old = devnull, new = Posix.FileSys.stderr};
          print ("Child says " ^ Int.toString i ^ "\n");
          print ("Child says " ^ Int.toString j ^ "\n");
          Posix.IO.close outfd;
          OS.Process.exit OS.Process.success
        end
      | SOME _ => (* ANALYZE THE TESTS'S OUTPUT *)
        let
          val () = Posix.IO.close outfd
          val chk = Posix.IO.readVec (infd, 1)
          val res = Posix.IO.readVec (infd, 1)
          val () = if Word8Vector.length chk = 1
                      andalso Word8Vector.sub (chk, 0) = 0wx1 
                   then () (* if Word8Vector.length res = 1 then ()
                         else raise Fail "Reading result bit failed!" *)
                   else raise Fail "Reading check bit failed!"
        in 
          if Word8Vector.length res <> 1 then BlewUp
          else case Word8Vector.sub (res, 0) of
                 0wx1 => CompileError
               | 0wx2 => SIGSEGV
               | 0wx3 => SIGFPE
               | 0wx4 => SIGALRM
               | 0wx5 => RuntimeError
               | 0wx6 => AssertionFailed
               | 0wx7 => ArrayOutOfBounds
               | 0wx10 => 
                 Return (from_wordlist (Posix.IO.readVec (infd, 4)))
               | _ => raise Fail "where'd that signal come from?"
        end
    end

  fun result_to_string (Return w) = "Program ran successfully with result "
                                  ^ Word32Signed.toString w
    | result_to_string SIGSEGV = "Program segfaulted"
    | result_to_string SIGFPE  = "Program divided by zero"
    | result_to_string SIGALRM = "Program timed out"
    | result_to_string CompileError = "Program failed to compile"
    | result_to_string RuntimeError = "Program had a runtime type error"
    | result_to_string BlewUp = "Unanticipated runtime error (Match?)"
    | result_to_string AssertionFailed = "Failed assertion"
    | result_to_string ArrayOutOfBounds = "Array out of bounds"

  fun did_return NONE (Return _) = true
    | did_return (SOME w) (Return w') = w = w'
    | did_return _ _ = false

  fun did_segfault r = r = SIGSEGV
  fun did_div_by_zero r = r = SIGFPE
  fun did_abort r = r = AssertionFailed orelse r = ArrayOutOfBounds
  fun did_infloop r = r = SIGALRM
  fun did_error r = r = CompileError orelse r = RuntimeError


end)
