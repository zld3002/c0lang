(* 
 * Simple symbolic debugger for the C0 Language
 *
 * Authors: Ian Gillis, Robert Simmons, Frank Pfenning
 *)

signature DEBUG =
sig
  (* Takes a the file name of a .c0 file to debug *)
  val debug : string *string list -> OS.Process.status
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
  \The following inputs allow you to control the codex.               \n\
  \ v           - Variables are displayed                             \n\
  \ h           - Help with this message                              \n\
  \ n           - Next, skipping over function calls                  \n\
  \ s           - Step, entering into function calls                  \n\
  \ <return>    - Same as s (step)                                    \n\
  \ e exp       - Evaluate exp in current context                     \n\
  \ r exp       - Run exp in step mode in current context             \n\
  \ q           - Exit codex                                          \n\
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
      | e => print "exception: unexpected exception\n"

  fun get_pos cmd = case cmd of
       C0.Exp(e, pos) => SOME(pos)
     | C0.Declare(t, x, SOME(e, pos)) => SOME(pos)
     | C0.Assign(opr_opt, e1, e2, pos) => SOME(pos)
     | C0.CCall(lv, f, args, pos) => SOME(pos)
     | C0.Assert(e, msg, pos) => SOME(pos)
     | C0.Error(e, pos) => SOME(pos)
     | C0.CondJump(e, pos, label) => SOME(pos)
     | C0.Return(SOME(e,pos)) => SOME(pos)
     (* C0.Label, C0.Declare(_,_,NONE), C0.Return(NONE), C0.PushScope, C0.PopScope _ *)
     | _ => NONE

  fun get_pos_source cmd = case get_pos cmd
   of SOME(pos) => Mark.show_source pos
    | NONE => C0.cmdToString cmd

  fun get_pos_string cmd = case get_pos cmd
   of SOME(pos) => Mark.show(pos)
    | NONE => ""

  fun is_invisible ((0,0),(0,0),_) = true
    | is_invisible pos = false

  fun is_silent cmd = case cmd of
       C0.Label(label, name) => true
     | C0.Exp(e, pos) => is_invisible pos
     | C0.Declare(tp, x, SOME(e, pos)) => is_invisible pos
     | C0.Declare(tp, x, NONE) => true (* decl w/o init always silent *)
     | C0.Assign(opr_opt, e1, e2, pos) => is_invisible pos
     | C0.CCall(lv_opt, f, args, pos) => is_invisible pos (* function call never silent? *)
     | C0.Assert(e, msg, pos) => is_invisible pos
     | C0.Error(e, pos) => is_invisible pos
     | C0.CondJump(e, pos, label) => is_invisible pos
     | C0.Jump(label) => true
     | C0.Return(SOME(e, pos)) => is_invisible pos
     | C0.Return(NONE) => true  (* return of void always silent *)
     | C0.PushScope => true
     | C0.PopScope(n) => true

  fun input_action next_cmd fname = 
      let
          val _ = if Flag.isset Flags.flag_emacs
                  then
                      println (get_pos_string next_cmd ^ " in function " ^ fname)
                  else
                      ( println (get_pos_string next_cmd ^ " in function " ^ fname)
                      ; print (get_pos_source next_cmd) )
          val _ = if Flag.isset Flags.flag_emacs
		  then print "(codex)\n"
		  else print "(codex) "
          val input = valOf (TextIO.inputLine TextIO.stdIn)
          val inputs = String.tokens Char.isSpace input
      in
          case inputs
           of ["v"] => LOCAL_VARS
            | ["vars"] => LOCAL_VARS
            | ["n"] => NEXT 1
            | ["n", tok] =>
              (case Int.fromString tok
                of NONE => IGNORE input
                 | SOME(i) => (if i > 0 then NEXT i else IGNORE input))
            | ["next"] => NEXT 1
            | ["next", tok] => 
              (case Int.fromString tok
                of NONE => IGNORE input
                 | SOME i => (if i > 0 then NEXT i else IGNORE input))
            | ["q"] => QUIT
            | ["quit"] => QUIT
            | ["h"] => HELP
            | ["help"] => HELP
            | [] => STEP 1
            | ["s"] => STEP 1
            | ["s", tok] =>
              (case Int.fromString tok
                of NONE => IGNORE input
                 | SOME i => (if i > 0 then STEP i else IGNORE input))
	    | ["step"] => STEP 1
            | ["step", tok] =>
              (case Int.fromString tok
                of NONE => IGNORE input
                 | SOME i => (if i > 0 then STEP i else IGNORE input))
            | "e" :: toks => EVAL_EXP (String.concatWith " " toks)
            | "eval" :: toks => EVAL_EXP (String.concatWith " " toks)
            | "r" :: toks => RUN_EXP (String.concatWith " " toks)
            | "run" :: toks => RUN_EXP (String.concatWith " " toks)
            | _ => IGNORE input
      end

(*------------- Expression evaluation -------------------*)

  fun reset_parser () =
      ( ParseState.reset()
      ; ErrorMsg.reset() )

  fun read_exp string =
   let 
      val () = reset_parser ()
      val () = ParseState.pushfile "<codex>"

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
          ; ParseState.reset () (* will remove pushed pseudofile "<codex>" *)
          ; ErrorMsg.reset () )
      end handle ErrorMsg.Error =>
                 ( ParseState.reset ()
                 ; ErrorMsg.reset () )

(*------------- Running expressions -----------------------*)
(*------------- Core I/O and evaluation -------------------*)
  
  fun init_fun (f, actual_args, formal_args, pos) = 
      ( State.push_fun (Exec.state, f, (f, pos))
      ; app (fn ((tp, x), v) => 
                ( State.declare (Exec.state, x, tp)
                ; State.put_id (Exec.state, x, v)))
            (ListPair.zip (formal_args, actual_args)))

  fun interact i j (cmds, labs) fname pc =
      let 
          val next_cmd = Vector.sub (cmds, pc) 
          val action = input_action next_cmd fname
      in
          case action
           of LOCAL_VARS => ( Exec.print_locals()
                            ; interact i j (cmds, labs) fname pc )
            | HELP =>       ( println help_message
                            ; interact i j (cmds, labs) fname pc ) 
            | QUIT =>       ( println "Goodbye!"
                            ; OS.Process.exit(OS.Process.success) )
            | IGNORE s =>   ( println ("Ignored command " ^ s)
                            ; interact i j (cmds, labs) fname pc )
            | EVAL_EXP "" => ( println "Need an expressing or assignment to evaluate"
                             ; interact i j (cmds, labs) fname pc )
            | EVAL_EXP e => ( eval_exp e
                            ; reset_parser()
                            ; interact i j (cmds, labs) fname pc ) 
            | RUN_EXP "" => ( println "Need an expression or assignment to run"
                            ; interact i j (cmds, labs) fname pc )
            | RUN_EXP e =>  ( run_exp e
                            ; reset_parser()
                            ; interact i j (cmds, labs) fname pc )
            | NEXT m =>     next_step (i,~1) (j,j+m) (cmds, labs) fname pc
            | STEP n =>     next_step (i,i+n) (j,~1) (cmds, labs) fname pc
          end

  and next_step (i,n) (j,m) (cmds, labs) fname pc =
      let
          val cmd = Vector.sub(cmds, pc)
      (*
          val _ = if is_silent cmd then print "$" else print "*"
          val _ = print (Int.toString i)
          val _ = println(":" ^ Int.toString(n) ^ ":" ^ C0.cmdToString (Vector.sub(cmds, pc)))
      *)
      in
          if is_silent cmd orelse (i <> n andalso j <> m)
          then one_step (i,n) (j,m) cmd (cmds, labs) fname pc
          else interact i j (cmds, labs) fname pc
      end

  and one_step (i,n) (j,m) cmd (cmds, labs) fname pc = case cmd of
      C0.CCall(NONE, f, args, pos) =>
      let
          val actual_args = List.map (Eval.eval_exp Exec.state) args
          val step_result = Exec.call_step(f, actual_args, pos) (* function call never silent? *)
          val (i',n') = fun_call (i+1,n) NONE f step_result actual_args pos
      in
          next_step (i',n') (j+1,m) (cmds, labs) fname (pc+1)
      end
    | C0.CCall(SOME(x), f, args, pos) => 
      let
          val loc = Eval.eval_lval Exec.state (C0.Var x)
          val actual_args = List.map (Eval.eval_exp Exec.state) args
          val step_result = Exec.call_step(f, actual_args, pos) (* function call never silent? *)
          val (i',n') = fun_call (i+1,n) (SOME(loc)) f step_result actual_args pos
      in
          next_step (i',n') (j+1,m) (cmds, labs) fname (pc+1)
      end
    | cmd =>
      case Exec.step ((cmds, labs), pc)
       of Exec.ReturnNone => (NONE, (i,if j <= m then i else n)) (* stop at caller if doing big-step *)
        | Exec.ReturnSome(res) => (SOME(res), (i,if j <= m then i else n))
        | Exec.PC(pc') => next_step (if is_silent cmd then i else i+1,n)
                                    (if is_silent cmd then j else j+1,m)
                                    (cmds, labs) fname pc'

  (* i has already been increased to account for the call itself *)
  and fun_call (i,n) dest f (Exec.Interp((_, formal_args), code)) actual_args pos = 
      let
          val _ = init_fun (f, actual_args, formal_args, pos)
          val (ret_val, (i',n')) = next_step (i,n) (0,~1) code (Symbol.name f) 0 (* exec function body *)
          val _ = State.pop_fun (Exec.state)
      in
          case (dest, ret_val)
           of (SOME(loc), SOME(v)) => ( Eval.put (Exec.state, loc, v) ; (i',n') )
            | (_, _) => (i',n')
      end
    | fun_call (i,n) (SOME(loc)) f (Exec.Native(res)) actual_args pos =
      ( Eval.put (Exec.state, loc, res) ; (i,n) )
    | fun_call (i,n) (NONE) f (Exec.Native(res)) actual_args pos = (i,n)

  and run_exp string =
      let
          val (cmds, labs) = read_exp string
          val (retval, (i',n')) = next_step (0,1) (0,~1) (cmds, labs) "_run_" 0 (* ignore return value *)
      in
          case retval
           of NONE => print ("finished run of '" ^ string ^ "'\n")
                      (* ^ "with last value " ^ State.value_string (Exec.last()) ^ "\n") *)
            | SOME(result) => print("finished run of '" ^ string ^ "' with value " 
                                    ^ ConcreteState.value_string result ^ "\n")
      end
      handle Error.Dynamic s => println ("<codex>:error: " ^ s)
           | Error.AssertionFailed s => println ("<codex>:" ^ s)
           | ErrorMsg.Error => ()
           | exn => ( print "exception: " ; print_exception exn )

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

  fun call_main (library_headers, program) run_arg =
      let
          val _ = init_state (library_headers, program)
      in
          run_exp (case run_arg
                    of NONE => "main()"
                     | SOME(exp_string) => exp_string)
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
      ( call_main (library_headers, program) (!Flags.run_call)
      ; OS.Process.success )
  end
  handle COMPILER_ERROR => OS.Process.failure (* message already printed *)
       | LINK_ERROR => (* some message printed, but not in error format *)
	 ( println (":error:could not link library")
	 ; OS.Process.failure )
       | _ => ( println (":error:unexpected exception")
	      ; OS.Process.failure )

end
