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
  "Codex - the C0 debugger.                                           \n\
  \                                                                   \n\
  \The code shown is the internal representation of your C0 program.  \n\
  \The debugger will display the NEXT command to be executed. To      \n\
  \proceed, hit enter, or any key other than the following special    \n\
  \inputs listed below. Default behavior is to step into function     \n\
  \calls.                                                             \n\
  \                                                                   \n\
  \The following inputs allow you to control the debugger.            \n\
  \ v           - Variables are displayed                             \n\
  \ h           - Help with this message                              \n\
  \ n           - Next, skipping over function calls                  \n\
  \ s           - Step, entering into function calls                  \n\
  \ <return>    - Same as s (step)                                    \n\
  \ e exp       - Evaluate exp in current context                     \n\
  \ r exp       - Run exp in step mode in current context             \n\
  \ q           - Exit the debugger                                   \n\
  \                                                                   \n"



  structure C0 = C0Internal
  structure State = ConcreteState

  exception COMPILER_ERROR 
  exception LINK_ERROR
  exception Internal of string

  datatype debug_action = 
     STEP of int
   | NEXT of int
   | LOCAL_VARS 
   | QUIT 
   | HELP
   | EVAL_EXP of string
   | RUN_EXP of string
   | IGNORE of string

  fun loop (f: unit -> unit) n =
     if n <= 0 then () else (f(); loop f (n-1))

(*-------------- Printing ----------------*)
  fun print s = TextIO.print s
  
  fun println s = ( TextIO.print s; TextIO.print "\n" )
  
  fun print_exception exn = 
     case exn of 
        Error.Uninitialized => 
           print "uninitialized value used\n"
      | Error.NullPointer => 
           print "attempt to dereference null pointer\n"
      | Error.ArrayOutOfBounds _ => 
           print "out of bounds array access\n"
      | Overflow => 
           print "integer overflow\n"
      | Div => 
           print "division by zero\n"
      | Error.ArraySizeNegative _ => 
           print "negative array size requested in allocation\n"
      | Error.Dynamic s => 
           print ("(ERROR IN DYNAMIC SEMANTICS, PLEASE REPORT): "^s)
      | Error.Internal s => 
           print ("(INTERNAL ERROR, PLEASE REPORT): "^s)
      | e => print "Exception: Unexpected exception\n"

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
        val _ = if Flag.isset Flags.flag_emacs
		then print "(codex)\n"
		else print "(codex) "
        val input = valOf (TextIO.inputLine TextIO.stdIn)
        val inputs = String.tokens Char.isSpace input
        val action = case inputs of 
            ["v"] => LOCAL_VARS
          | ["vars"] => LOCAL_VARS
          | ["n"] => NEXT 1
          | ["next"] => NEXT 1
          | ["next", tok] => 
              (case Int.fromString tok of 
                  NONE => IGNORE input
                | SOME i => (if i > 0 then NEXT i else IGNORE input))
          | ["q"] => QUIT
          | ["quit"] => QUIT
          | ["h"] => HELP
          | ["help"] => HELP
          | [] => STEP 1
          | ["s"] => STEP 1
	  | ["step"] => STEP 1
          | ["step", tok] =>
              (case Int.fromString tok of 
                  NONE => IGNORE input
                | SOME i => (if i > 0 then STEP i else IGNORE input))
          | "e" :: toks => EVAL_EXP (String.concatWith " " toks)
          | "eval" :: toks => EVAL_EXP (String.concatWith " " toks)
          | "r" :: toks => RUN_EXP (String.concatWith " " toks)
          | "run" :: toks => RUN_EXP (String.concatWith " " toks)
          | _ => IGNORE input
      in 
        action 
      end
    else NEXT 1
  end 

(*------------- Expression evaluation -------------------*)

  fun reset_parser () =
      ( ParseState.reset()
      ; ErrorMsg.reset() )

  fun read_exp string =
   let 
      val () = ParseState.reset ()
      val () = ParseState.pushfile "<codex>"
      val () = ErrorMsg.reset ()

      (* Lex the string, append a semicolon so we can parse as a statement. *)

      (* Why is the second argument, lexpos, 2? I'm cribbing off of 
       * what coin does here, nothing more. - rjs 8/24/2012 *)
      val (tokstream, _, lex_state) =
          C0Lex.lineLexer
              (Stream.fromList (explode string @ [#";"]), 2, C0Lex.normal)
      val () = if !ErrorMsg.anyErrors then raise ErrorMsg.Error else ()
      val () = if lex_state = C0Lex.normal 
                  then ()
               else ( print "<codex>:error: incomplete expression\n"
                    ; raise ErrorMsg.Error)

      (* Parse the tokens, enforce that we only accept expressions and assignments *)

      (* It could be easy to handle other statements! We're actually
       * artifically stopping this from happening with this function, which 
       * errors upon encountering anything that's not a list. Declarations
       * would need to be noticed and avoided, I think. 
       * - rjs 8/24/2012 *)
      fun assert_exp stm = 
      let fun not_expected s =
           ( print ("<codex>:error: expected an expression or assignment, found " ^ s ^ "\n")
           ; raise ErrorMsg.Error)
      in
         case stm of 
            Ast.Markeds stm => assert_exp (Mark.data stm)
          | Ast.Assign _ => ()
          | Ast.Exp exp => ()
          | Ast.Seq _ => not_expected "a block statement"
          | Ast.StmDecl _ => not_expected "a variable declaration"
          | Ast.If _ => not_expected "an if statement"
          | Ast.While _ => not_expected "a while loop"
          | Ast.For _ => not_expected "a for loop"
          | Ast.Continue => not_expected "a continue"
          | Ast.Break => not_expected "a break"
          | Ast.Return _ => not_expected "a return"
          | Ast.Assert _ => not_expected "an assertion"
          | Ast.Error _ => not_expected "an error" 
          | Ast.Anno _ => not_expected "an annotation"
      end

      val stm = 
         case Parse.parse_stm (Stream.force tokstream) of
            (* I think this can't happen... the parser fails earlier. *)
            NONE => 
            ( print "<codex>:error: incomplete expression\n"
            ; raise ErrorMsg.Error ) 
  
            (* Handles 'e 12' 'e 14 + 14' 'e return' 'e x = 12' *)
          | SOME (stm, Stream.Cons ((Terminal.EOL, _), _)) => 
            ( assert_exp stm
            ; stm )

            (* Handles 'e 12;' 'e x = 12;' *)
          | SOME (stm, Stream.Cons ((Terminal.SEMI, _), _)) =>
             ( assert_exp stm (* Prioritize this error message *)
             ; print ("<codex>:error: expression should not be followed by \
                      \semicolon\n")
             ; raise ErrorMsg.Error )

            (* Handles 'e {}' 'e 16; {}' 'e 12; 12; 12' *)
          | SOME (stm, Stream.Cons ((_, _), _)) =>
             ( assert_exp stm (* Prioritize this error message *)
             ; print ("<codex>:error: expected an expression or assignment, \
                      \found multiple statements\n")
             ; raise ErrorMsg.Error )

          | SOME (stm, Stream.Nil) => (* should be impossible *)
            ( println ("<codex>:error: unexpected end of input")
            ; raise ErrorMsg.Error )

      val () = if !ErrorMsg.anyErrors then raise ErrorMsg.Error else ()

      (* Typecheck, isolate, compile *)
      val env = State.local_tys Exec.state
      val processed_stm = TypeChecker.typecheck_interpreter env stm (* might raise ErrorMsg.Error *)
      val isolated_stms = Isolate.iso_stm env stm
      val (cmds, labs) = Compile.cStms isolated_stms ((~1,~1),(~1,~1),"<BUG>") 
      val cmds = Vector.concat [ cmds, Vector.fromList [ C0.Return NONE ] ]
   in
       (cmds, labs)
   end

  fun eval_exp string = 
      (* lex, parse, type-check, elaborate *)
      let val (cmds, labs) = read_exp string
          (* Run *)
          val _ = Exec.exec (cmds, labs)
                  handle Error.AssertionFailed s => 
                         ( print ("<codex>:" ^ s ^"\n")
                         ; raise ErrorMsg.Error )
                       | exn => 
                         ( print "<codex>:"
                         ; print_exception exn
                         ; raise ErrorMsg.Error ) 
      in
          ( print (State.value_string (Exec.last ())^"\n")
          ; ParseState.reset ()
          ; ErrorMsg.reset () )
      end handle ErrorMsg.Error =>
                 (ParseState.reset () ; ErrorMsg.reset ())

(*------------- Running expressions -----------------------*)
(*------------- Core I/O and evaluation -------------------*)
  
  fun init_fun(f, actual_args, formal_args, pos) = 
      ( State.push_fun (Exec.state, f, (f, pos))
      ; app (fn ((tp, x), v) => 
                ( State.declare (Exec.state, x, tp)
                ; State.put_id (Exec.state, x, v)))
            (ListPair.zip (formal_args, actual_args)))

  fun sim_fun_call dest f (Exec.Interp((_, formal_args), code)) actual_args pos = 
      let
          val _ = init_fun(f, actual_args, formal_args, pos)
          val ret_val = dstep code (Symbol.name f) 0
          val _ = State.pop_fun (Exec.state)
      in
          case (dest, ret_val)
           of (SOME(loc), SOME(v)) => Eval.put (Exec.state, loc, v)
            | (_, _) => ()
      end 
    | sim_fun_call (SOME(loc)) f (Exec.Native(res)) actual_args pos =
        Eval.put (Exec.state, loc, res)
    | sim_fun_call (NONE) f (Exec.Native(res)) actual_args pos = ()

  and run_exp string =
      let
          val (cmds, labs) = read_exp string
          val _ = dstep (cmds, labs) "_run_" 0 (* ignore return value *)
      in
          print ("Finished run of '" ^ string ^ "' with value " 
                 ^ State.value_string (Exec.last ()) ^ "\n")
      end
      handle Error.Dynamic s => println ("<codex>:error: " ^ s)
           | Error.AssertionFailed s => println ("<codex>:" ^ s)
           | ErrorMsg.Error => ()
           | Option => println "<codex>: quit run" (* should be impossible *)
           | exn => ( print "exception: " ; print_exception exn )

  and dstep (cmds,labs) fname pc = 
      let 
          val next_cmd = Vector.sub (cmds, pc) 
          val action = io next_cmd fname
      in
          case action
            of LOCAL_VARS => ( Exec.print_locals()
                             ; dstep (cmds, labs) fname pc )
             | HELP =>       ( println help_message
                             ; dstep (cmds, labs) fname pc ) 
             | QUIT =>       ( println "Goodbye!"
                             ; OS.Process.exit(OS.Process.success) )
             | IGNORE s =>   ( println ("Ignored command " ^ s)
                             ; dstep (cmds, labs) fname pc )
             | EVAL_EXP "" => ( println "Need an expressing or assignment to evaluate"
                              ; dstep (cmds, labs) fname pc )
             | EVAL_EXP e => ( eval_exp e
                             ; reset_parser()
                             ; dstep (cmds, labs) fname pc ) 
             | RUN_EXP "" => ( println "Need an expression or assignment to run"
                             ; dstep (cmds, labs) fname pc)
             | RUN_EXP e =>  ( run_exp e
                             ; reset_parser()
                             ; dstep (cmds, labs) fname pc )
             | NEXT i =>     next (cmds, labs) fname pc
             | STEP i =>     step_into next_cmd (cmds, labs) fname pc
      end

  and next (cmds, labs) fname pc =
      (case Exec.step ((cmds, labs), pc)
        of Exec.ReturnNone => NONE
         | Exec.ReturnSome(res) => SOME(res)
         | Exec.PC(pc') => dstep (cmds, labs) fname pc')

  and step_into next_cmd (cmds, labs) fname pc = case next_cmd of
      C0.CCall(NONE, f, args, pos) =>
      let
          val actual_args = List.map (Eval.eval_exp Exec.state) args
          val _ = sim_fun_call NONE f (Exec.call_step(f, actual_args, pos)) actual_args pos
      in
          dstep (cmds, labs) fname (pc+1)
      end
    | C0.CCall(SOME(x), f, args, pos) => 
      let
          val loc = Eval.eval_lval Exec.state (C0.Var x)
          val actual_args = List.map (Eval.eval_exp Exec.state) args
          val _ = sim_fun_call (SOME(loc)) f (Exec.call_step(f, actual_args, pos)) actual_args pos
      in
          dstep (cmds, labs) fname (pc+1)
      end
    | _ => next (cmds, labs) fname pc

  fun dstep_top (cmds, labs) fname =
      dstep (cmds, labs) fname 0
      handle Error.Dynamic(s) => ( println (":error: " ^ s) ; NONE )

(*--------- Load libraries and call main -------------*)
   fun raiseSignal sgn = 
    ( Posix.Process.kill (Posix.Process.K_PROC (Posix.ProcEnv.getpid ()), sgn)
    ; raise Fail "Well, this is ironic (unreachable exception).")

  fun assertLibrariesLoaded lib = 
      case CodeTab.lookup lib of 
         NONE => raise LINK_ERROR
       | SOME (CodeTab.Native _) => ()
       | SOME (CodeTab.AbsentNative _) => raise LINK_ERROR
       | SOME (CodeTab.Interpreted _) => ()
       | SOME (CodeTab.Builtin _) => ()

  fun init_state (library_headers, program) =
      ( ConcreteState.clear_locals Exec.state
      ; CodeTab.reload_libs (!Flags.libraries)
      ; CodeTab.reload (library_headers @ program)
      ; app assertLibrariesLoaded (CodeTab.list ()) )

  fun call_main (library_headers, program) NONE =
      let
          val _ = init_state (library_headers, program)
          val init_call = Exec.call_step (Symbol.symbol "main", [], ((0, 0), (0, 0), "_init_"))
	  val code = case init_call
		      of Exec.Interp(_,code) => code
		       | _ => raise Internal("Main function was tagged as native\n")
      in
	  (dstep_top code "main")
	  handle Error.AssertionFailed s => ( println s ; NONE )
               | Option => (print "Goodbye\n"; NONE)
               | exn => 
                 ( print "Exception: "
                 ; print_exception exn
                 ; NONE)
      end
    | call_main (library_headers, program) (SOME(run_call)) =
      let
          val _ = init_state (library_headers, program)
      in
          ( run_exp run_call    (* handles its own exceptions?? *)
          ; NONE )
      end

(* ----------- Top level function ------------*)
  fun debug (name,args) =
  let
   (* Get the sources file from the compiler *)
   val () = Top.reset ()
   val sources = 
      Top.get_sources_set_flags
        {options = Flags.core_options @ Flags.coin_options @ Flags.codex_options,
         errfn = fn msg => println msg,
         versioninfo = 
            "C0 debugger (codex) " ^ Version.version 
            ^ " (r" ^ BuildId.revision ^ ", " ^ BuildId.date ^ ")",
         usageinfo = 
         GetOpt.usageInfo 
           {header = "Usage: codex [OPTIONS_AND_SOURCEFILES...]",
            options = Flags.core_options @ Flags.coin_options @ Flags.codex_options},
         args = args}
      handle _ => raise COMPILER_ERROR 
  
  (* Typecheck, enforcing the presence of a correctly-defined main function *)
   val main = Symbol.symbol "main" 

   val {library_headers, program, oprogram} = 
   let 
      val maindecl = Ast.Function (main, Ast.Int, [], NONE, nil, false, NONE)
   in
       ( Symtab.bind (main, maindecl)
       (* ; Symset.add main *) (* do not force 'main' to be defined. Jan 1, 2013 -fp  *)
       ; Top.typecheck_and_load sources )
   end handle _ => raise COMPILER_ERROR

   val {library_wrappers} = 
       Top.finalize {library_headers = library_headers}
       handle _ => raise COMPILER_ERROR
 
   val () =
       Top.static_analysis oprogram 
       handle _ => raise COMPILER_ERROR      

   val () = Builtins.reset {argv = rev (!Flags.runtime_args)}

   val () = case (!Flags.run_call, Symtab.lookup main)
             of (NONE, SOME(Ast.Function(_, _, _, NONE, _, _, _))) =>
                ( println ("<codex>:error: " ^ "function 'main' not defined\n"
                           ^ "use -r '<call>' to specify another function call to debug")
                ; raise COMPILER_ERROR )
              | (_, _) => ()

  in
      (case call_main (library_headers, program) (!Flags.run_call)
	of SOME(retval) =>
	   ( println ("main function returned "
		      ^ ConcreteState.value_string retval) ;
	     SOME(retval))
	 | NONE => NONE) (* error: message already printed *)
  end
  handle COMPILER_ERROR => NONE (* message already printed *)
       | LINK_ERROR => (* some message printed, but not in error format *)
	 ( println (":error:could not link library")
	 ; NONE )
       | _ => ( println (":error:unexpected exception")
	      ; NONE )

end
