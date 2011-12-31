structure Messages = struct

val p = fn s => print (s ^ "\n") 

fun help x =
let in
p"List of commands:";
p"";
p"e/evaluate <some expression>";
p"  Returns result of evaluating <some expression> in the current environment.";
p"  E.g. \"e 4 + 7 * 2\" causes the debugger to say \"Value: 18 (int)\",";
p"  and \"e true + 4\" causes the debugger to say \"cannot cast bool to int\".";
p"s/step";
p"  Step fowards, possibly entering a function.";
p"  Just pressing <Enter> will also step the debugger forwards.";
p"n/next";
p"  Go to next statement in the current function.";
p"c/continue";
p"  Run until the program finishes or is interrupted by CTRL-C.";
p"q/quit";
p"  Exit the debugger.";
p"h/help";
p"  Display this help message.";
x
end

(*
fun help x = 
let in
p"List of commands:\n";
p"e/evaluate <some expression>";
p"  Returns result of evaluating <some expression> in the current environment.";
p"  E.g. \"e 4 + 7 * 2\" causes the debugger to print \"Value: 18 (int)\",";
p"  and \"e true + 4\" causes the debugger to print \"XXX\".";
p"s/step";
p"  Step fowards, possibly entering a function.";
p"n/next (Unimplemented)";
p"  Go to next statement in the current function.";
p"c/continue";
p"  Go to the next breakpoint.";
p"rs/reverse-step (Unimplemented)";
p"  Rewind one step, possibly entering a function.";
p"rn/reverse-next (Unimplemented)";
p"  Rewind to the previous statement in the current function.";
p"rc/reverse-continue (Unimplemented)";
p"  Rewind to the previous breakpoint.";
p"q/quit";
p"  Exit the debugger.";
p"h/help";
p"  Display this help message.";
p"";
x
end
*)

end


structure Runline :> RUNLINE = struct
		    
  datatype status = CONTINUE | EXIT of OS.Process.status

  fun args(_,_) = CONTINUE

  (* Pretties it up a bit *)
  type 'a oref = 'a option ref
  val get = fn x => valOf (! x)
  val put = fn (x, y) => x := SOME y

  (* Stored state *)
  type stuff = (C0.var_name * CFG.pc * (CFG.pc -> CFG.pc CFG.node))
  val program    : CFG.prog oref = ref NONE
  val state      : stuff State.state oref = ref NONE
  val mark       : Mark.ext oref = ref NONE
  val checkpoint : stuff State.checkpoint oref = ref NONE
  val position   : OpSem.position oref = ref NONE

  fun show_final v : status = 
    let in 
      print "Finished with value ";
      print (Word32Signed.toString (State.to_int v));
      print "\n";
      CONTINUE
    end

  fun show_pc () : unit = 
    let in
      print (Mark.show (get mark));
      print (" in function ");
      print (State.current_function (get state));
      print ("\n")
    end

  fun step_to_pos prog state x : unit = 
    let val y = OpSem.step prog state x in
      case #2 y of
        CFG.Stmt (_,SOME pos,_) =>     (put (mark, pos); put (position, y))
      | CFG.Test (_,SOME pos,_,_) =>   (put (mark, pos); put (position, y))
      | CFG.Return (_,SOME pos) =>     (put (mark, pos); put (position, y))
      | CFG.Assert (_,_,pos,_) =>      (put (mark, pos); put (position, y))
      | CFG.Call (_,_,_,pos,_) =>      (put (mark, pos); put (position, y))
      | _ => step_to_pos prog state y
    end

  fun step () : status = 
    let val state = get state in
      put (checkpoint, State.checkpoint state);
      step_to_pos (get program) state (get position);
      show_pc ();
      CONTINUE
    end handle OpSem.Done (_, v) => show_final v

  fun continue () : status = 
    let val state = get state in
      put (checkpoint, State.checkpoint state);
      step_to_pos (get program) state (get position);
      continue ()
    end handle OpSem.Done (_, v) => show_final v

  fun next depth : status = 
    let val state = get state in
      put (checkpoint, State.checkpoint state);
      step_to_pos (get program) state (get position);
      if State.call_depth state <= depth
      then (show_pc (); CONTINUE)
      else next depth
    end handle OpSem.Done (_, v) => show_final v

  fun evaluate s : status =
    let in
      case Parser.parse_exp s of
        NONE => (print "Could not parse expression.\n"; CONTINUE)
      | SOME exp => 
        (print (State.value_string (Eval.eval_exp (get state, exp)) ^ "\n"); 
         CONTINUE)
    end handle Error.Dynamic s => 
               (print ("Evaluation error: " ^ s ^ "\n"); CONTINUE)
             | _ => (print ("Unexpected error\n"); CONTINUE)

  fun runline s = 
    let in
      case hd (String.fields (fn x => x = #" " orelse x = #"\n") s) of 
        ""                 => step () 
      | "e"                => evaluate (String.extract (s,1,NONE))
      | "evaluate"         => evaluate (String.extract (s,8,NONE))
      | "locals"           => (State.print_locals (get state); CONTINUE)
      | "s"                => step () 
      | "step"             => step () 
      | "n"                => next (State.call_depth (get state))
      | "next"             => next (State.call_depth (get state))
      | "c"                => continue ()
      | "continue"         => continue ()
      | "q"                => EXIT(OS.Process.success)
      | "quit"             => EXIT(OS.Process.success)
      | "h"                => Messages.help CONTINUE
      | "help"             => Messages.help CONTINUE
      | _ => 
        let in
          print "Invalid command.\n"; 
          print "Type \"help\" (without the quotes) for a list of commands.\n";
          CONTINUE
        end
    end

  fun restart () : unit = 
    let in
      case !checkpoint of 
        NONE => () (* First time restart is called checkpoint is not set *)
      | SOME checkpoint => State.restore (get state, checkpoint);
      show_pc ()
    end
    
  fun start (s, args) = 
    let in
      print "c0de (alpha 3) - The c0 debugger.\n";
      print "Type \"help\" (without the quotes) for a list of commands.\n";
      case args of
        [] => raise Error.Dynamic ("Usage : " ^ s ^ " <args>")
      | files =>
        let
          (* XXX Use Frank's parser/typechecker first! *)

          (* Parse and elaborate *)
          val () = print ("Parsing... ")
          val c0_prog = List.concat (Parser.parse_list files)
            handle exn => (print (exnName exn ^ " - " ^ exnMessage exn ^ "\n"); raise Error.Internal ("unexpected problem re-parsing."))
          val () = print ("elaborating... ")
          val cfg_prog = Flatten.flatten (MkGraph.mkprog true c0_prog)
            handle _ => raise Error.Internal ("unexpected problem making CFG.")
          val () = print ("done.\n")

          (* Initalize and step to position *)
          val main = 
              case CFG.functions cfg_prog "main" of
                NONE => raise Error.Dynamic ("no main function to run")
              | SOME main => main
          val new_state = 
              State.new_state 
                  {ty_vars = CFG.ty_vars cfg_prog, 
                   st_defs = CFG.struct_defs cfg_prog, 
                   fun_defs = CFG.fun_defs cfg_prog,
                   initial_function = "main"}
          
        in
          put (program, cfg_prog);
          put (state, new_state);
          step_to_pos cfg_prog new_state (CFG.graph main, CFG.entry_point main)
        end
    end



(*


  fun show_pc (state, extern_pc) : status = 

  fun step () : status = 
    case (Eval.step (valOf (!stored_state))) of
      (prog, graph, (state, Eval.Done v)) => show_final v
    | (prog, graph, (state, Eval.More pc)) =>
      (stored_state := SOME (prog, graph, state, pc);
       case pc of 
         Eval.Step intern_pc =>
         (case MapI.find (#pc_to_extern graph, intern_pc) of 
            NONE => step () | SOME extern_pc => show_pc (state, extern_pc))
       | _ => step ())

  fun next () : status = (print "unimplemented\n"; CONTINUE)

  fun continue () = 
    case (Eval.step (valOf (!stored_state))) of
      (prog, graph, (state, Eval.Done v)) => show_final v
    | (prog, graph, (state, Eval.More pc)) => 
      (stored_state := SOME (prog, graph, state, pc); continue ())


  fun reverse_step () : status = (print "unimplemented\n"; CONTINUE)
  fun reverse_next () : status = (print "unimplemented\n"; CONTINUE)
  fun reverse_continue () : status = (print "unimplemented\n"; CONTINUE)
*)

(*             

  fun show_pc () : status = 
    let in
      print (Mark.show (!stored_pos));
      print (" in function ");
      print (C0.id_string (CState.current_function (#2 (!stored_state))));
      print ("\n");
      CONTINUE
    end

  fun show_final v : status = 
    let in 
      print "Finished with value ";
      print (IntInf.toString (Word32.toLargeInt (CState.to_int v)));
      print "\n";
      CONTINUE
    end

  fun step () : status = 
    let in
      step_to_pos (!stored_prog) (!stored_state);
      show_pc ()
    end
    handle OpSem.Done (_, v) => show_final v

  fun continue () : status = 
    let in 
      step_to_pos (!stored_prog) (!stored_state);
      continue ()
    end
    handle OpSem.Done (_, v) => show_final v

  fun evaluate s : status =
    let val state = #2 (!stored_state) in
      case Parser.parse_exp s of
        NONE => raise Error.Dynamic "ill-formed expression."
      | SOME exp =>  
        let val (state, v) = CEval.eval_exp (state, exp) in
          print ("Value " ^ CState.stringify v ^ "\n"); CONTINUE
        end
    end
*)

  (* 
    case (Eval.step (valOf (!stored_state))) of
      (prog, graph, (state, Eval.Done v)) => show_final v
    | (prog, graph, (state, Eval.More pc)) =>
      (stored_state := SOME (prog, graph, state, pc);
       case pc of 
         Eval.Step intern_pc =>
         (case MapI.find (#pc_to_extern graph, intern_pc) of 
            NONE => step () | SOME extern_pc => show_pc (state, extern_pc))
       | _ => step ())
*)

(*

  fun runline s = 
    let in
      case hd (String.fields (fn x => x = #" " orelse x = #"\n") s) of 
        ""                 => step () 
      | "e"        => evaluate (String.extract (s,1,NONE))
      | "evaluate" => evaluate (String.extract (s,8,NONE))
(*
      | "n"                => next ()
      | "next"             => next ()
*)
(*
      | "rs"               => reverse_step ()
      | "reverse-step"     => reverse_step ()
      | "rn"               => reverse_next ()
      | "reverse-next"     => reverse_next ()
      | "rc"               => reverse_continue ()
      | "reverse-continue" => reverse_continue ()
*)
      | "h"                => Messages.help CONTINUE
      | "help"             => Messages.help CONTINUE
      | _ => 
        let in
          print "Invalid command.\n"; 
          print "Type \"help\" (without the quotes) for a list of commands.\n";
          CONTINUE
        end
    end

  fun start (s,args) = 
    let in
      print "c0de (alpha 3) - The c0 debugger.\n";
      print "Type \"help\" (without the quotes) for a list of commands.\n";
      case args of
        [] => raise Error.Dynamic ("Usage : " ^ s ^ " <args>")
      | files =>
        let
          val () = print ("Parsing... ")
          (* XXX Use Frank's parser/typechecker first! *)
                   
          val () = print ("elaborating... ")
          val c0_prog = List.concat (Parser.parse_list files)
            handle _ => raise Error.Internal ("unexpected problem re-parsing.")
          val cfg_prog = Flatten.flatten (MkGraph.mkprog c0_prog)
            handle _ => raise Error.Internal ("unexpected problem making CFG.")

          val fn_prog = CFG.functions cfg_prog
          val main = case (fn_prog ("main", NONE)) of
                       NONE => raise Error.Dynamic ("no main function to run")
                     | SOME main => main
          val state = CState.new_state {ty_vars = CFG.ty_vars cfg_prog, 
                                        st_defs = CFG.struct_defs cfg_prog, 
                                        functions = CFG.list_functions cfg_prog,
                                        initial_function = ("main", NONE)}

          val () = print ("done.\n")
        in 
          stored_prog := fn_prog;
          step_to_pos fn_prog (CFG.graph main, state, CFG.entry_point main)
        end
    end

*)
end

structure Server =
  Server (structure Runline = Runline
          structure SigINT = SigINT) 
