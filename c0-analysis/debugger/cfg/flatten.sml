(* Flattening out control flow graphs *)

signature FLATTEN = sig

  (* Flattens out a control flow graph, introducing Call nodes and removing
   * all occurances of the expression C0.Call (e, es, pos) *)
  val flatten : CFG.prog -> CFG.prog

end

structure Flatten :> FLATTEN = struct

  local val x = ref 0 in 
  fun gen_resid () = ("res", SOME (x := !x + 1; !x))
  end

  val pushed_scopes = ref 0

  (* and pop_a_lot (parent_next, n) =
        if n <= 0 then parent_next
        else let
          val next = ref NONE
          val this = emit (PopScope next)
        in 
          parent_next := SOME this;
          pop_a_lot (next, n-1)
        end *)

  val append = GrowArray.append

  fun flatten_exp nodes exp = 
    let val f = flatten_exp nodes in
      case exp of 
        C0.Const c              => C0.Const c
      | C0.Var x                => C0.Var x
      | C0.Binop (e1, oper, e2) => C0.Binop (f e1, oper, f e2)
      | C0.Ref e                => C0.Ref (f e)
      | C0.Monop (oper, e)      => C0.Monop (oper, f e)
      | C0.Postop (e, oper)     => C0.Postop (f e, oper)
      | C0.Index (e1, e2)       => C0.Index (f e1, f e2)
      | C0.RefField (e, fld)    => C0.RefField (f e, fld)
      | C0.Field (e, fld)       => C0.Field (f e, fld)
      | C0.Alloc t              => C0.Alloc t
      | C0.AllocArray (t, e)    => C0.AllocArray (t, f e)
      | C0.Length e             => C0.Length (f e)
      | C0.Result               => C0.Result
      | C0.Old e                => C0.Old (f e)
      | C0.Call (e, es, pos)    =>
        let 
          val e = f e
          val es = map f es
          val x = gen_resid ()
          val pc = GrowArray.length nodes
        in
          pushed_scopes := !pushed_scopes + 1;
          append nodes (CFG.Call (x, e, es, pos, pc + 1));
          C0.Var x
        end

      (* XXX eventually would like to fix this *)
      | C0.Ternary (e, eT, eF) => C0.Ternary (f e, f eT, f eF)
    end

  fun flatten_node nodes (pc, node) = 
    let 
      val () = pushed_scopes := 0
      val next_pc = GrowArray.length nodes
      val f = flatten_exp nodes
      val updated_node = 
          case node of 
            CFG.Stmt (C0.Noop, pos, next) => node
                                             
          | CFG.Stmt (C0.Exp e, pos, next) =>
            CFG.Stmt (C0.Exp (f e), pos, next)

          | CFG.Stmt (C0.Assign (e1, oper, e2), pos, next) =>
            CFG.Stmt (C0.Assign (f e1, oper, f e2), pos, next)

          | CFG.PushScope next => node

          | CFG.PopScope (next, n) => node

          | CFG.Declare (ty, x, next) => node

          | CFG.Test (e, pos, nextT, nextF) => 
            CFG.Test (f e, pos, nextT, nextF)

          | CFG.Return (NONE, pos) => node

          | CFG.Return (SOME e, pos) =>
            CFG.Return (SOME (f e), pos)

          | CFG.Assert (e1, e2, pos, next) =>
            CFG.Assert (f e1, f e2, pos, next)

          | CFG.Call (x, e, es, pos, next) =>
            CFG.Call (x, f e, map f es, pos, next)
            
      val new_length = GrowArray.length nodes
      val popped = !pushed_scopes
      exception Impossible
    in
      (* If nothing was added to the vector, then updated_node = node *)
      if new_length = next_pc then ()
      else 
        ((* Replace the entry point with the first addition to the vector *)
         GrowArray.update nodes pc (GrowArray.sub nodes next_pc);
         
         (* Now we'll need to patch some things up; we'll try reuse that
          * position that we freed up when we moved the entry point. *)
         case updated_node of 
           CFG.Stmt (stmt, pos, next) => 
           (append nodes (CFG.Stmt (stmt, pos, next_pc));
            GrowArray.update nodes next_pc (CFG.PopScope (next, popped)))
         | CFG.Test (e, pos, nextT, nextF) =>
           (append nodes (CFG.Test (e, pos, new_length + 1, next_pc));
            append nodes (CFG.PopScope (nextT, popped));
            GrowArray.update nodes next_pc (CFG.PopScope (nextF, popped)))
         | CFG.Return (e, pos) =>
           (append nodes (CFG.Return (e, pos))) (* Can't reuse position *)
         | CFG.Assert (e1, e2, pos, next) => 
           (append nodes (CFG.Assert (e1, e2, pos, next_pc));
            GrowArray.update nodes next_pc (CFG.PopScope (next, popped)))
         | CFG.Call (x, e, es, pos, next) =>
           (append nodes (CFG.Call (x, e, es, pos, next_pc));
            GrowArray.update nodes next_pc (CFG.PopScope (next, popped)))
         | _ => raise Impossible)
    end
        
  fun flatten_graph {entry_point, nodes} = 
    let
      val node_array = GrowArray.tabulate 
                      (Vector.length nodes)
                      (fn x => Vector.sub (nodes, x))
    in
      Vector.appi (flatten_node node_array) nodes;
      {entry_point = entry_point, 
       nodes = Array.vector (GrowArray.finalize node_array)}
    end

  fun flatten_function (CFG.Int {return_type, args, graph}) =
      CFG.Int {return_type = return_type,
               args = args,
               graph = flatten_graph graph}
    | flatten_function (CFG.Ext x) = CFG.Ext x

  fun flatten {functions, ty_vars, struct_defs} = 
    {functions = CFG.MapS.map flatten_function functions,
     ty_vars = ty_vars,
     struct_defs = struct_defs}

end
