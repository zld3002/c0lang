structure CoinExec:>sig

   (* The "go" function never returns *)
   val go: string * string list -> 'a
  
end = 
struct

(* Finishing with the right error messages *)

type status = Word8.word * string
fun die (x, msg) = (print msg; Posix.Process.exit x)
val GREAT_SUCCESS: status    = (0wx0, "")
val WRITE_ERROR: status      = (0wx1, "Could not write to file\n")
val COMPILER_ERROR: status   = (0wx2, "Did not compile\n")
val LINK_ERROR: status       = (0wx3, "Some libraries did not link\n")
val EXIT_FAILURE: status     = (0wx4, "")
fun RUNTIME_ERROR s: status  = (0wx5, "Internal bug in coin: " ^ s ^ "\n")

structure FS = Posix.FileSys

(* Handle command line name and arguments *)
fun go (name, args) = 
let

   (* Get the sources files from the compiler *)
   val () = Top.reset ()
   val sources = 
      Top.get_sources_set_flags
        {options = Flags.core_options,
         errfn = fn msg => die COMPILER_ERROR,
         versioninfo = 
            "CoinExec " ^ Version.version 
            ^ " (r" ^ BuildId.revision ^ ", " ^ BuildId.date ^ ")",
         usageinfo = 
         GetOpt.usageInfo 
           {header = "Usage: " ^ name
                     ^ " coinexec [OPTIONS_AND_SOURCEFILES...]",
            options = Flags.core_options},
         args = args}
      handle _ => die COMPILER_ERROR

   (* Typecheck, enforcing the presence of a correctly-defined main function *)

   val {library_headers, program, oprogram} = 
   let 
      val main = Symbol.symbol "main" 
      val maindecl = Ast.Function (main, Ast.Int, [], NONE, nil, false, NONE)
   in
      Symtab.bind (main, maindecl)
    ; Symset.add main
    ; Top.typecheck_and_load sources
   end handle _ => die COMPILER_ERROR

   val {library_wrappers} = 
      Top.finalize {library_headers = library_headers}
       handle _ => die COMPILER_ERROR

   val () =
      Top.static_analysis oprogram 
       handle _ => die COMPILER_ERROR      

   (* Check environment variable, start outputting data *)

   val writeArr: Word8Array.array -> unit =
   let 
      fun createf file = FS.createf (file, FS.O_WRONLY, FS.O.trunc, FS.S.irwxu)
      val file = Option.map createf (Posix.ProcEnv.getenv "C0_RESULT_FILE")
   in
      case file of 
         NONE => (fn _ => ())
       | SOME fd => (fn arr => 
                        (if Posix.IO.writeArr (fd, Word8ArraySlice.full arr)
                              < Word8Array.length arr
                         then die WRITE_ERROR
                         else ())
                        handle _ => die WRITE_ERROR)
   end handle _ => die WRITE_ERROR


   (* Load code and libraries into interpreter, run the interpreter *)

   fun assertLibrariesLoaded lib = 
      case CodeTab.lookup lib of 
         NONE => die LINK_ERROR
       | SOME (CodeTab.Native _) => ()
       | SOME (CodeTab.AbsentNative _) => die LINK_ERROR
       | SOME (CodeTab.Interpreted _) => ()
       | SOME (CodeTab.Builtin _) => ()

   fun raiseSignal sgn = 
    ( Posix.Process.kill (Posix.Process.K_PROC (Posix.ProcEnv.getpid ()), sgn)
    ; raise Fail "Well, this is unexpected (unreachable exception).")

   (* write initial 0x0 byte *)
   val () = writeArr (Word8Array.fromList [ 0wx0 ])

   val result =
   let in
    ( ConcreteState.clear_locals Exec.state
    ; CodeTab.reload_libs (!Flags.libraries)
    ; CodeTab.reload (library_headers @ program)
    ; app assertLibrariesLoaded (CodeTab.list ())
    ; Exec.call (Symbol.symbol "main", [], ((0, 0), (0, 0), "_init_")))
   end handle Error.NullPointer => 
              (print "attempt to dereference null pointer\n"
               ; raiseSignal Posix.Signal.segv)
            | Error.ArrayOutOfBounds _ => 
              (print "Out of bounds array access\n"
               ; raiseSignal Posix.Signal.segv)
            | Overflow => raiseSignal Posix.Signal.fpe
            | Div => raiseSignal Posix.Signal.fpe 
            | Error.ArraySizeNegative _ => 
              (print "Negative array size requested in allocation\n"
               ; raiseSignal Posix.Signal.segv)
            | Error.AssertionFailed s => 
              (print (s ^ "\n")
               ; raiseSignal Posix.Signal.abrt)
            | Error.ErrorCalled s => 
              (print ("Error: " ^ s ^ "\n")
               ; die EXIT_FAILURE)
            | Error.Uninitialized => die (RUNTIME_ERROR "Uninitialized data")
            | Error.Allocation => die (RUNTIME_ERROR "Can't allocate memory")
            | Error.Compilation => die (RUNTIME_ERROR "Code transformation")
            | Error.Internal s => die (RUNTIME_ERROR s)
            | Error.Dynamic s => die (RUNTIME_ERROR s)



   (* Report results *)

   val arr = Word8Array.fromList [ 0wx0, 0wx0, 0wx0, 0wx0 ]
   val word32_res = ConcreteState.to_int result

   (* XXX Why does PackWord32Little want to take a Word64.word??? *)
   val word64_res = Word32.toLargeWord word32_res

   val () = PackWord32Little.update (arr, 0, word64_res)
   val () = writeArr arr
   val () = print (Word32Signed.toString word32_res ^ "\n")
in 
   die GREAT_SUCCESS 
end handle _ => die WRITE_ERROR

end
