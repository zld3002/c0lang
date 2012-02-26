(* Running with the Cymbol...   *)
(* Robert J. Simmons            *)


signature RUNNER = sig

  val run : string -> Word32.word

end

structure Runner (* :> RUNNER *) = struct

  fun run filename =
    let
      val parsed = #1 (Parser.parse filename)
      val graphed = MkGraph.mkprog parsed
      val ans = Eval.run graphed
    in
      ans
    end

  val stored_marks : Mark.ext vector ref = ref (Vector.fromList [])
 
  val stored_state : (CFG.program *
                      CFG.graph *
                      Eval.state * 
                      Eval.pc) option ref = ref NONE

  fun print_state () = 
    let val (prog, graph, state, pc) = valOf (!stored_state) 
    in State.print_state state end

  fun evaluate exp = 
    let val (prog, graph, state, pc) = valOf (!stored_state) in
      case Parser.parse_string exp of
        NONE => print "Ill-formed expression.\n"
      | SOME exp =>  
        let val (state, v) = EvalExp.eval (state, exp) in
          print ("Expression has value " ^ State.stringify v ^ "\n")
        end
    end

  fun show extern_pc = Mark.show (Vector.sub (!stored_marks, extern_pc))

  fun step () = 
    case (Eval.step (valOf (!stored_state))) of
      (prog, graph, (state, Eval.Done v)) => 
      let in
        print ("Execution finished with value " ^
               IntInf.toString (Word32.toLargeInt (State.to_int (valOf v))) ^ 
               "\n");
        stored_state := NONE
      end
    | (prog, graph, (state, Eval.More (pc as Eval.Step intern_pc))) => 
      let in
        case MapI.find (#pc_to_extern graph, intern_pc) of
          NONE => (stored_state := SOME (prog, graph, state,pc); step ())
        | SOME extern_pc => 
          (print ("At function " ^ State.current_function state ^ 
                  " position " ^ show extern_pc ^ "\n");
           stored_state := SOME (prog, graph, state, pc))
      end
    | (prog, graph, (state, Eval.More (pc as Eval.StepIn _))) => 
      let in
        print ("Entering into function " ^
               State.current_function state ^ "\n");
        stored_state := SOME (prog, graph, state, pc);
        step ()
      end

    | (prog, graph, (state, Eval.More (pc as Eval.StepOut _))) => 
      let in
        print ("Returning to function " ^
               State.current_function state ^ "\n");
        stored_state := SOME (prog, graph, state, pc);
           step ()
      end

  fun init filename = 
    let
      val (parsed, marks) = Parser.parse filename
      val prog = MkGraph.mkprog parsed

      val main_graph = #graph (MapS.lookup (#functions prog, "main"))
      val (state, entry_point) = Eval.start prog "main"
      val state = State.put_magic_function (state, Eval.magic_function prog)
    in
      stored_marks := marks;
      stored_state := SOME (prog, main_graph, state, entry_point);
      step()
    end

end
