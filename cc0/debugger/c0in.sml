structure Messages = struct

val p = fn s => print (s ^ "\n") 

fun help x =
let in
p"List of commands - currently most functionaliy is turned off.";
p"";
p"Press <enter> or type \"s\" to step to the next command in the program.";
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

  (* Stored state: nasty default values in order to not have valOf... *)
  val stored_pos   : Mark.ext ref = ref ((0,0),(0,0),"")
  val stored_prog  : (C0.fun_name -> CFG.function option) ref = 
      ref (fn _ => raise Match)
  val stored_state : ((CFG.pc -> CFG.pc CFG.node) * 
                      (C0.var_name * CFG.pc) CState.state *
                      CFG.pc CFG.node) ref = 
      ref (fn _ => raise Match,
           CState.new_state {ty_vars = fn _ => raise Match,
                             st_defs = fn _ => raise Match,
                             initial_function = ("xxx", NONE),
                             magicfun = NONE},
           CFG.Stmt (C0.Noop, NONE, 0))


(*

  fun show_final v : status = 
    let in 
      print "Finished with value ";
      print (IntInf.toString (Word32.toLargeInt (State.to_int (valOf v))));
      print "\n";
      CONTINUE
    end

  fun show_pc (state, extern_pc) : status = 
    let in
      print (Mark.show (Vector.sub (!stored_marks, extern_pc)));
      print (" in function " ^ State.current_function state ^ "\n");
      CONTINUE
    end

  fun evaluate s : status =
    let val (prog, graph, state, pc) = valOf (!stored_state) in
      case Parser.parse_string s of
        NONE => raise Error.Dynamic "ill-formed expression."
      | SOME exp =>  
        let val (state, v) = EvalExp.eval_exp (state, exp) in
          print ("Value " ^ State.stringify v ^ "\n"); CONTINUE
        end
    end

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
             
  fun step_to_pos prog x = 
    let val y = OpSem.step prog x in
      case #3 y of
        CFG.Stmt (_,SOME pos,_) =>   (stored_state := y; stored_pos := pos)
      | CFG.Test (_,SOME pos,_,_) => (stored_state := y; stored_pos := pos)
      | CFG.Return (_,SOME pos) =>   (stored_state := y; stored_pos := pos)
      | CFG.Call (_,_,_,pos,_) =>    (stored_state := y; stored_pos := pos)
      | _ => step_to_pos prog y
    end

  fun show_pc () : status = 
    let in
      print (Mark.show (!stored_pos));
      print (" in function ");
      print (C0.id_string (CState.current_function (#2 (!stored_state))));
      print ("\n");
      CONTINUE
    end

  fun step () : status = 
    let in
      step_to_pos (!stored_prog) (!stored_state);
      show_pc ()
    end
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

  fun runline s = 
    let in
      case hd (String.fields (fn x => x = #" " orelse x = #"\n") s) of 
        ""                 => step () 
      | "s"                => step () 
      | "step"             => step () 
(*
      | "e"        => evaluate (String.extract (s,1,NONE))
      | "evaluate" => evaluate (String.extract (s,8,NONE))
      | "n"                => next ()
      | "next"             => next ()
      | "c"                => continue ()
      | "continue"         => continue ()
      | "rs"               => reverse_step ()
      | "reverse-step"     => reverse_step ()
      | "rn"               => reverse_next ()
      | "reverse-next"     => reverse_next ()
      | "rc"               => reverse_continue ()
      | "reverse-continue" => reverse_continue ()
      | "q"                => EXIT(OS.Process.success)
      | "quit"             => EXIT(OS.Process.success)
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
      print "c0de (alpha 2) - The c0 debugger.\n";
      print "Type \"help\" (without the quotes) for a list of commands.\n";
      case args of
        [] => raise Error.Dynamic ("Usage : " ^ s ^ " <args>")
      | files =>
        let
          val () = print ("Parsing... ")
          (* XXX Use Frank's parser/typechecker first! *)
                   
          val () = print ("elaborating... ")
          val c0_prog = List.concat (map Parser.parse files)
            handle _ => raise Error.Internal ("unexpected problem re-parsing.")
          val cfg_prog = Flatten.flatten (MkGraph.mkprog c0_prog)
            handle _ => raise Error.Internal ("unexpected problem making CFG.")

          val fn_prog = CFG.functions cfg_prog
          val main = case (fn_prog ("main", NONE)) of
                       NONE => raise Error.Dynamic ("no main function to run")
                     | SOME main => main
          val state = CState.new_state {ty_vars = CFG.ty_vars cfg_prog, 
                                        st_defs = CFG.struct_defs cfg_prog, 
                                        magicfun = NONE,
                                        initial_function = ("main", NONE)}

          val () = print ("done.\n")
        in 
          stored_prog := fn_prog;
          step_to_pos fn_prog (CFG.graph main, state, CFG.entry_point main)
        end
    end

end

structure Server =
  Server (structure Runline = Runline
          structure SigINT = SigINT) 
