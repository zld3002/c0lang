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
  \ s           - Step, entering into function calls                  \n\
  \ <return>    - Same as s (step)                                    \n\
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
   | IGNORE of string

  fun loop (f: unit -> unit) n =
     if n <= 0 then () else (f(); loop f (n-1))

(*-------------- Printing ----------------*)
  fun print s = TextIO.print s
  
  fun println s = TextIO.print (s^"\n")
  
  fun print_exception exn = 
     case exn of 
        Error.Uninitialized => 
           print "uninitialized value used\n"
      | Error.NullPointer => 
           print "attempt to dereference null pointer\n"
      | Error.ArrayOutOfBounds _ => 
           print "Out of bounds array access\n"
      | Overflow => 
           print "Integer overflow\n"
      | Div => 
           print "Division by zero\n"
      | Error.ArraySizeNegative _ => 
           print "Negative array size requested in allocation\n"
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
		then print "(code)\n"
		else print "(code) "
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
          | _ => IGNORE input
      in 
        action 
      end
    else NEXT 1
  end 

(*------------- Expression evaluation -------------------*)

  fun eval_exp string = 
   let 
      val () = ParseState.reset ()
      val () = ParseState.pushfile "<debugger>"
      val () = ErrorMsg.reset ()

      (* Lex the string, append a semicolon so we can parse as a statement. *)
      exception Lexer
      (* Why is the second argument, lexpos, 2? I'm cribbing off of 
       * what coin does here, nothing more. - rjs 8/24/2012 *)
      val (tokstream, _, lex_state) =
         C0Lex.lineLexer
            (Stream.fromList (explode string @ [#";"]), 2, C0Lex.normal)
      val () = if !ErrorMsg.anyErrors then raise Lexer else ()
      val () = if lex_state = C0Lex.normal 
                  then ()
               else (print "Error: incomplete syntax\n"; raise Lexer) 

      (* Parse the tokens, enforce that we only accept expressions *)
      exception Parser

      (* It could be easy to handle other statements! We're actually
       * artifically stopping this from happening with this function, which 
       * errors upon encountering anything that's not a list. Declarations
       * would need to be noticed and avoided, I think. 
       * - rjs 8/24/2012 *)
      fun assert_exp stm = 
      let fun not_expected s =
           ( print ("<debugger>:expected an expression, got "^s^"\n")
           ; raise Parser)
      in
         case stm of 
            Ast.Markeds stm => assert_exp (Mark.data stm)
          | Ast.Assign _ => not_expected "an assignment"
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
          | Ast.Anno _ => not_expected "an annotation"
      end

      val stm = 
         case Parse.parse_stm (Stream.force tokstream) of
            (* I think this can't happen... the parser fails earlier. *)
            NONE => 
             ( print "<debugger>:incomplete syntax\n"
             ; raise Parser) 
  
            (* Handles 'e 12' 'e 14 + 14' 'e return' 'e x = 12' *)
          | SOME (stm, Stream.Cons ((Terminal.EOL, _), _)) => 
             ( assert_exp stm
             ; stm)

            (* Handles 'e 12;' 'e x = 12;' *)
          | SOME (stm, Stream.Cons ((Terminal.SEMI, _), _)) =>
             ( assert_exp stm (* Prioritize this error message *)
             ; print ("<debugger>:expression should not be followed by \
                      \semicolon\n")
             ; raise Parser)

            (* Handles 'e {}' 'e 16; {}' 'e 12; 12; 12' *)
          | SOME (stm, Stream.Cons ((_, _), _)) =>
             ( assert_exp stm (* Prioritize this error message *)
             ; print ("<debugger>:expected an expression, \
                      \got multiple statements\n")
             ; raise Parser)

          | SOME (_, Stream.Nil) => 
             ( print ("<debugger>:Invariant failed! No semicolon. (BUG!)\n")
             ; raise Parser)

      val () = if !ErrorMsg.anyErrors then raise Parser else ()

      (* Typecheck, isolate, compile *)
      val env = State.local_tys Exec.state
      val processed_stm = TypeChecker.typecheck_interpreter env stm
      val isolated_stms = Isolate.iso_stm env stm
      val (cmds, labs) = Compile.cStms isolated_stms ((~1,~1),(~1,~1),"<BUG>") 
      val cmds = Vector.concat [ cmds, Vector.fromList [ C0.Return NONE ] ]
     
      (* Run *)
      exception Run
      val _ = Exec.exec (cmds, labs)
               handle Error.AssertionFailed s => 
                       ( print ("<debugger>:"^s^"\n")
                       ; raise Run)
                    | exn => 
                       ( print "<debugger>:"
                       ; print_exception exn
                       ; raise Run) 
   in
    ( print (State.value_string (Exec.last ())^"\n")
    ; ParseState.reset ()
    ; ErrorMsg.reset ())
   end handle _ => (ParseState.reset (); ErrorMsg.reset ())

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
        
      fun next (cmds,labs,pc) =
        (case Exec.step ((cmds,labs),pc) of
        Exec.ReturnNone => NONE
      | Exec.ReturnSome(res) => SOME(res)
      | Exec.PC(i) => dstep' i)
    in
      case action
       of LOCAL_VARS => (Exec.print_locals(); dstep' pc)
        | HELP => (println help_message; dstep' pc) 
        | QUIT => (println "Goodbye!"; OS.Process.exit(OS.Process.success))
        | IGNORE s => (println ("Ignored command "^s); dstep' pc)
        | EVAL_EXP "" => (println "Need an argument (try 'eval 4')"; dstep' pc)
        | EVAL_EXP e => (eval_exp e; dstep' pc) 
        | NEXT i => next(cmds,labs,pc)
        | STEP i => 
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
            | _ => next(cmds,labs,pc))
    end
  in
    (dstep' 0)
    handle Error.Dynamic(s) => (println (":error: "^s); NONE)
  end

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


  fun call_main (library_headers, program) =
      let
        val _ = (ConcreteState.clear_locals Exec.state
        ; CodeTab.reload_libs (!Flags.libraries)
        ; CodeTab.reload (library_headers @ program)
        ; app assertLibrariesLoaded (CodeTab.list ()))
   
        val init_call = Exec.call_step (Symbol.symbol "main", [], ((0, 0), (0, 0), "_init_"))
	val code = case init_call
		    of Exec.Interp(_,code) => code
		     | _ => raise Internal("Main function was tagged as native\n")
      in
	  (dstep code "main")
	  handle Error.AssertionFailed s => (print (s^"\n"); NONE)
               | Option => (print "Goodbye\n"; NONE)
               | exn => 
                  ( print "Exception: "
                  ; print_exception exn
                  ; NONE)
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
            "code " ^ Version.version 
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
      (case call_main (library_headers, program)
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
