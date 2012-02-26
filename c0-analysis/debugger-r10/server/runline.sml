(* Trivial implementations of the Runline signature (echo) *)

structure Messages = struct

val p = fn s => print (s ^ "\n") 

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

end

structure Runline :> RUNLINE = struct
		    
  datatype status = CONTINUE | EXIT of OS.Process.status

  fun args(_,_) = CONTINUE

  val stored_marks : Mark.ext vector ref = ref (Vector.fromList [])
 
  val stored_state : (CFG.program *
                      CFG.graph *
                      Eval.state * 
                      Eval.pc) option ref = ref NONE

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
                  
  fun runline s = 
    let in
      case hd (String.fields (fn x => x = #" " orelse x = #"\n") s) of 
        "e"        => evaluate (String.extract (s,1,NONE))
      | "evaluate" => evaluate (String.extract (s,8,NONE))
      | ""                 => step () 
      | "s"                => step () 
      | "step"             => step () 
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
      print "c0de (alpha 1) - The c0 debugger.\n";
      print "Type \"help\" (without the quotes) for a list of commands.\n";
      case args of
        [ filename ] => 
        let
          val () = print ("File " ^ filename ^ ": parsing... ")
          (* XXX Use Frank's parser/typechecker first! *)
                   
          val () = print ("elaborating... ")
          val (parsed, marks) = Parser.parse filename
            handle _ => raise Error.Internal ("unexpected problem re-parsing.")
          val prog = MkGraph.mkprog parsed   
            handle _ => raise Error.Internal ("unexpected problem making CFG.")
          val () = print ("loading... ")
          val main_graph = #graph (MapS.lookup (#functions prog, "main"))
              handle _ => raise Error.Dynamic ("no function main().")
          val (state, entry_point) = Eval.start prog "main"
          val state = State.put_magicfun (state, Eval.magicfun prog)
          val () = print ("done.\n")
                   
        in 
          stored_marks := marks;
          stored_state := SOME (prog, main_graph, state, entry_point);
          ignore (step ())
        end
      | _ => raise Error.Dynamic ("Usage : " ^ s ^ " <args>")
    end
    
end

structure Server =
  Server (structure Runline = Runline
          structure SigINT = SigINT) 
