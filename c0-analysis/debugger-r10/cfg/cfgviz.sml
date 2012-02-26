(* Visualizing C0 control flow graphs *)
(* Robert J. Simmons                  *)

signature CFG_VIZ = sig

  val gviz : CFG.graph * string -> unit  

end

structure CFGViz :> CFG_VIZ = struct

  fun gviz (prog, filename) = raise Match
(*
    let
      val {entry_point, nodes, pc_to_extern, extern_to_pc} = construct_graph vec
      val outstream = TextIO.openOut filename
      fun print s = TextIO.output (outstream, s)
      fun str pc = 
          case MapI.find (pc_to_extern, pc) of
            NONE =>
            "\"" ^ Int.toString pc ^ "\""
          | SOME extern_pc => 
            "\"" ^ Int.toString pc ^ " : " ^ Int.toString extern_pc ^ "\""
      fun gviz_one (pc, (node, depth)) =
        case node of 
          Command {next,...} =>    
          let in
            print ("   node [shape = circle]; " ^ str pc ^ ";\n");
            "   " ^ str pc ^ " -> " ^ str next ^ " [];\n"
          end
        | FunctionCall {next,...} =>    
          let in
            print ("   node [shape = circle]; " ^ str pc ^ ";\n");
            "   " ^ str pc ^ " -> " ^ str next ^ " [];\n"
          end
        | Test {nextT,nextF,...} => 
          let in   
            print ("   node [shape = circle]; " ^ str pc ^ ";\n");
            "   " ^ str pc ^ " -> " ^ str nextT ^ " [ label = \"T\" ];\n" ^
            "   " ^ str pc ^ " -> " ^ str nextF ^ " [ label = \"F\" ];\n" 
          end
        | Return {...} =>
          let in
            print ("   node [shape = doublecircle]; " ^ str pc ^ ";\n"); ""
          end
    in
      print "digraph finite_state_machine {\n";
      print "   rankdir=LR;\n";
      print "   size=\"8,5\"";
      Vector.app print (Vector.mapi gviz_one nodes);
      print "}\n";
      TextIO.closeOut outstream
    end
*)

end
