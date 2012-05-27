(* 
 * Simple symbolic debugger for the C0 Language
 *
 * Authors: Ian Gillis, Robert Simmons
 *)

signature DEBUG =
sig
  (* Takes a the file name of a .c0 file to debug *)
  val debug : (string*string list) -> ConcreteState.value option
end

structure Debug = 
struct

  val help_message = 
  "Code - the C0 debugger.                                            \n\
  \                                                                   \n\
  \The code shown is the internal representation of your C0 program.  \n\
  \The debugger will display the NEXT command to be executed. To      \n\
  \proceed, hit enter, or any key other than the following special    \n\
  \inputs listed below. Default behavior is to step into function     \n\
  \calls.                                                             \n\
  \                                                                   \n\
  \The following inputs allow you to control the debugger.            \n\
  \ v           - Display local variables                             \n\
  \ h           - Display this help message                           \n\
  \ n           - Execute command, skipping over function calls       \n\
  \ q           - Exit the debugger                                   \n\
  \                                                                   \n"



  structure C0 = C0Internal
  structure State = ConcreteState

  exception COMPILER_ERROR 
  exception LINK_ERROR
  exception Internal of string

  datatype debug_action = STEP | NEXT | LOCAL_VARS | QUIT | HELP

(*-------------- Printing ----------------*)
  fun print s = TextIO.print s
  
  fun println s = TextIO.print (s^"\n")
  
  fun check_pos ((0,0),(0,0),_) = false
    | check_pos pos = true 

  fun get_pos_string c =
  case c of (C0.Exp(e,pos)) =>
    (check_pos pos, Mark.show pos)
    | (cmd as (C0.Assign(binop,e1,e2,pos))) =>
        (check_pos pos,Mark.show pos)
    | (cmd as (C0.CCall(target,f,args,pos))) => 
        (check_pos pos,Mark.show pos)
    | (cmd as (C0.Assert(e,s,pos))) =>
        (check_pos pos,Mark.show pos)
    | (cmd as (C0.Return(SOME(e,pos)))) =>
        (check_pos pos,Mark.show pos)
    | (cmd as (C0.Declare(tau,x,SOME(e,pos)))) =>
        (check_pos pos,Mark.show pos)
    | cmd => (false,"")

  fun get_comm_string c =
  case c of (C0.Exp(e,pos)) => 
        (check_pos pos,C0.cmdToString c)
    | (cmd as (C0.Assign(binop,e1,e2,pos))) =>
        (check_pos pos,C0.cmdToString c)
    | (cmd as (C0.CCall(target,f,args,pos))) => 
        (check_pos pos,C0.cmdToString c)
    | (cmd as (C0.Assert(e,s,pos))) =>
        (check_pos pos,C0.cmdToString c)
    | (cmd as (C0.Return(SOME(e,pos)))) =>
        (check_pos pos,C0.cmdToString c)
    | (cmd as (C0.Declare(tau,x,SOME(e,pos)))) =>
        (check_pos pos,C0.cmdToString c)
    | cmd => (false,"")

  fun io next_cmd fname = 
  let
    val (to_print,s) = if Flag.isset Flags.flag_emacs then
                          get_pos_string next_cmd
                       else get_comm_string next_cmd
  in
    if to_print then
      let
        val _ = println (s^" in function "^fname)
        val _ = print "(code) "
        val input = valOf (TextIO.inputLine TextIO.stdIn)
        val action = case input of 
            "v\n" => LOCAL_VARS
          | "vars\n" => LOCAL_VARS
          | "n\n" => NEXT
          | "next\n" => NEXT
          | "q\n" => QUIT
          | "quit\n" => QUIT
          | "h\n" => HELP
          | "help\n" => HELP
          | _ => STEP
      in 
        action 
      end
    else NEXT
  end 

(*------------- Core I/O and evaluation -------------------*)
  
  fun init_fun(f,actual_args,formal_args,pos) = 
        (
        State.push_fun (Exec.state, f, (f, pos));
        app (fn ((tp, x), v) => 
          (State.declare (Exec.state, x, tp);
        State.put_id (Exec.state, x, v)))
        (ListPair.zip (formal_args, actual_args)))


  fun dstep (cmds,labs) fname = 
  let
    fun dstep' pc = 
    let
      val next_cmd = Vector.sub (cmds,pc) 
      val action = io next_cmd fname
        
      fun eval (cmds,labs,pc) =
        (case Exec.step(cmds,labs,pc) of
        Exec.ReturnNone => NONE
      | Exec.ReturnSome(res) => SOME(res)
      | Exec.PC(i) => dstep' i)
    in
      case action of LOCAL_VARS => (Exec.print_locals(); dstep' pc)
        | HELP => (println help_message; dstep' pc) 
        | QUIT => (println "Goodbye!"; OS.Process.exit(OS.Process.success))
        | STEP => 
        (case next_cmd of C0.CCall(NONE,f,args,pos) =>
          let
            val actual_args = List.map (Eval.eval_exp Exec.state) args
          in
          (case Exec.call_step(f,actual_args,pos) of 
            Exec.Interp((_,formal_args),code) => 
                   (init_fun(f,actual_args,formal_args,pos);
                    let
                      val _ = dstep code (Symbol.name f) in () end;
                    let val _ = State.pop_fun (Exec.state) in () end;
                    dstep' (pc+1))
          | Exec.Native(res) => dstep' (pc+1))
          end
            | C0.CCall(SOME(x),f,args,pos) => 
              let
                val loc = Eval.eval_lval Exec.state (C0.Var x)
                val actual_args = List.map (Eval.eval_exp Exec.state) args

                fun sim_fun_call (Exec.Native(res)) = 
                    ( Eval.put (Exec.state,loc,res);
                      dstep' (pc+1))
                  | sim_fun_call (Exec.Interp((_,formal_args),code)) = 
                  let
                    val _ = init_fun(f,actual_args,formal_args,pos)
                    val ret_val = dstep code (Symbol.name f)
                    val _ = State.pop_fun (Exec.state)
                    val _ = case ret_val of SOME(v) => 
                        Eval.put (Exec.state,loc,v)
                                          | NONE => ()
                  in
                    dstep' (pc+1)
                  end
              in
                sim_fun_call (Exec.call_step(f,actual_args,pos))
              end
            | _ => eval(cmds,labs,pc))
        | NEXT => eval(cmds,labs,pc)
    end
  in
    (case dstep' 0 of NONE =>  NONE
                   | SOME(res) => SOME(res))
    handle Error.Dynamic(s) => (println ("Error: "^s); NONE)
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
        case init_call of (Exec.Interp(_,code)) => dstep code "main" 
                        | _ => raise Internal("Main function was tagged as native\n")
      end

(* ----------- Top level function ------------*)
  fun debug (name,args) =
  let
   (* Get the sources file from the compiler *)
   val () = Top.reset ()
   val sources = 
      Top.get_sources_set_flags
        {options = Flags.core_options @ Flags.coin_options @ Flags.code_options,
         errfn = fn msg => println msg,
         versioninfo = 
            "CoinExec " ^ Version.version 
            ^ " (r" ^ BuildId.revision ^ ", " ^ BuildId.date ^ ")",
         usageinfo = 
         GetOpt.usageInfo 
           {header = "Usage: " ^ name
                     ^ " code [OPTIONS_AND_SOURCEFILES...]",
            options = Flags.core_options @ Flags.coin_options @ Flags.code_options},
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
