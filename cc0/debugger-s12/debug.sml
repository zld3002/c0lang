(* 
 * Simple symbolic debugger for the C0 Language
 *
 * Author: Ian Gillis
 *)

signature DEBUG =
sig
  (* Takes a the file name of a .c0 file to debug *)
  val debug : (string*string list) -> unit
end

structure Debug = 
struct
  exception COMPILER_ERROR 
  exception LINK_ERROR
  exception Internal of string

(*-------------- Printing ----------------*)
  fun print s = TextIO.print s
  fun println s = TextIO.print (s^"\n")

  (*fun print_scope decls =
          app (fn (x, (_,v)) => 
                  print (Symbol.name x ^ " --> " ^ State.value_string v ^ "\n"))
              (Symbol.elemsi decls)*)


(*------------- Core I/O and evaluation -------------------*)
  fun dstep (cmds,labs) = 
  let
    fun dstep' pc = 
    let
      val next_cmd = Vector.sub (cmds,pc) 
      val next_cmd_s = C0Internal.cmdToString(next_cmd)
      val _ = println ("  "^next_cmd_s)
      val _ = print "$ "
      val input = valOf (TextIO.inputLine TextIO.stdIn)
      val eval = case String.compare (input,"vars\n") of 
          EQUAL => ((Exec.print_locals());false)
        | _ => true
    in
      if eval then 
      case Exec.step(cmds,labs,pc) of
        Exec.ReturnNone => NONE
      | Exec.ReturnSome(res) => SOME(res)
      | Exec.PC(i) => dstep' i
      else
        dstep' pc
    end
  in
    case dstep' 0 of NONE => println "void"
                   | SOME(res) => println ("  "^(ConcreteState.value_string res) )
  end

(*--------- Load libraries and call main -------------*)
  fun assertLibrariesLoaded lib = 
      case CodeTab.lookup lib of 
         NONE => raise LINK_ERROR
       | SOME (CodeTab.Native _) => ()
       | SOME (CodeTab.AbsentNative _) => raise LINK_ERROR
       | SOME (CodeTab.Interpreted _) => ()

  fun call_main(library_headers,program) =
      let
        val _ = (ConcreteState.clear_locals Exec.state
        ; CodeTab.reload_libs (!Flags.libraries)
        ; CodeTab.reload (library_headers @ program)
        ; app assertLibrariesLoaded (CodeTab.list ()))
      
        val init_call = Exec.call_step (Symbol.symbol "main", [], ((0, 0), (0, 0), "_init_"))
      in
        case init_call of (Exec.Interp(_,code)) => dstep code 
                        | _ => raise Internal("Main function was tagged as native\n")
      end

(* ----------- Top level function ------------*)
  fun debug (name,args) =
  let
   (* Get the sources file from the compiler *)
   val () = Top.reset ()
   val sources = 
      Top.get_sources_set_flags
        {options = Flags.core_options,
         errfn = fn msg => println msg,
         versioninfo = 
            "CoinExec " ^ Version.version 
            ^ " (r" ^ BuildId.revision ^ ", " ^ BuildId.date ^ ")",
         usageinfo = 
         GetOpt.usageInfo 
           {header = "Usage: " ^ name
                     ^ " coinexec [OPTIONS_AND_SOURCEFILES...]",
            options = Flags.core_options},
         args = args}
      handle _ => raise COMPILER_ERROR 
  
  (* Typecheck, enforcing the presence of a correctly-defined main function *)

   val {library_headers, program} = 
   let 
      val main = Symbol.symbol "main" 
      val maindecl = Ast.Function (main, Ast.Int, [], NONE, nil, false, NONE)
   in
      Symtab.bind (main, maindecl)
    ; Symset.add main
    ; Top.typecheck_and_load sources
   end handle _ => raise COMPILER_ERROR

   val {library_wrappers} = 
      Top.finalize {library_headers = library_headers}
       handle _ => raise COMPILER_ERROR
    
  in
    call_main(library_headers,program)
  end


end
