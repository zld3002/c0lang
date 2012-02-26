structure SimpleHandler :> WEB_HANDLER = struct
		    
  open DefaultHandler

  val gensymb = let val x = ref 0 in fn () => (x := !x + 1; x) end
 
  structure MapI = 
  SplayMapFn(struct type ord_key = int val compare = Int.compare end)

  val stored_progs : {pos   : Mark.ext,
                      prog  : C0.fun_name -> CFG.function option,
                      graph : CFG.pc -> CFG.pc CFG.node,
                      state : (C0.var_name * CFG.pc) CState.state,
                      next  : CFG.pc CFG.node} MapI.map ref = MapI.empty

(*
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
*)

  fun build_reply 

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

  fun restart () = ignore (show_pc ())

  fun runline s = 
    let in
      case hd (String.fields (fn x => x = #" " orelse x = #"\n") s) of 
        ""                 => step () 
      | "s"                => step () 
      | "step"             => step () 
      | "e"        => evaluate (String.extract (s,1,NONE))
      | "evaluate" => evaluate (String.extract (s,8,NONE))
(*
      | "n"                => next ()
      | "next"             => next ()
*)
      | "c"                => continue ()
      | "continue"         => continue ()
(*
      | "rs"               => reverse_step ()
      | "reverse-step"     => reverse_step ()
      | "rn"               => reverse_next ()
      | "reverse-next"     => reverse_next ()
      | "rc"               => reverse_continue ()
      | "reverse-continue" => reverse_continue ()
*)
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
                                        (* XXX needs magicfun *)
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
