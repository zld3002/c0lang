(* Transforming the concrete C0 syntax into C0 control flow graphs *)
(* *)

signature MK_GRAPH = sig

  exception GraphConstruction 

  val mkgraph : C0.statement list -> CFG.graph
  val mkprog  : C0.program -> CFG.program

end

structure MkGraph :> MK_GRAPH = struct

  open CFG
  structure GA = GrowArray

  exception GraphConstruction 

  (* Internal state of the control flow graph construction, and operations *)
  datatype cfg_state 
    = X 
    | S of {break_pc : intern_pc, continue_pc : intern_pc, break_depth : int}

  fun push_scope X = X
    | push_scope (S {break_pc, continue_pc, break_depth}) = 
      S {break_pc = break_pc, 
         continue_pc = continue_pc,
         break_depth = break_depth + 1}

  fun push_loop _ (break_pc, continue_pc) = 
      S {break_pc = break_pc, continue_pc = continue_pc, break_depth = 0}

  fun get_break X = raise GraphConstruction
    | get_break (S data) = data

  type proto_graph = ((intern_pc option ref) node * extern_pc option) vector

  (* Takes a list of statements and turns it into a proto-graph *)
  fun build_graph stmts : proto_graph =
    let
      val nodes : ((intern_pc option ref) node * extern_pc option) GA.growarray
        = GA.empty ()
          
      (* Emitting a node returns the new internal PC referring to that node *)
      fun emit (node, extern_pc) =
        let val intern_pc = GA.length nodes in
          GA.update nodes intern_pc (node, extern_pc); 
          intern_pc
        end

      (* process() takes a statement and an unitialized program counter. It
       * intializes the program counter, and returns a new program counter
       * that needs to be initialized. *)
      fun process_list (parent_next, []) cfg_state = parent_next
        | process_list (parent_next, stmt :: stmts) cfg_state = 
          process_list (process (parent_next, stmt) cfg_state, stmts) cfg_state

      and pop_a_lot (parent_next, n) =
        if n <= 0 then parent_next
        else let
          val next = ref NONE
          val this = emit (PopScope next, NONE)
        in 
          parent_next := SOME this;
          pop_a_lot (next, n-1)
        end

      and process (parent_next, stmt) cfg_state : intern_pc option ref = 
        let 
          (* This will be the unitialized pc we return. *)
          val next : intern_pc option ref = ref NONE

          (* This will be the node that we use to intalize parent_next. *)
          val intern_pc = 
              case stmt of 
                C0.Decl(ty,x,exp,extern_pc) => 
                emit (Decl(ty,x,exp,next), SOME extern_pc)

              | C0.Simple(C0.Assign(ret,oper,
                                    C0.Call(C0.Func(lhs,exps,extern_pc)),_)) => 
                emit (Call(SOME ret,lhs,exps,next), SOME extern_pc)

              | C0.Simple(C0.Assign(lhs,oper,exp,extern_pc)) => 
                emit (Assign(lhs,oper,exp,next), SOME extern_pc)

              | C0.Simple(C0.SimpleCall(C0.Func(lhs,exps,extern_pc))) => 
                emit (Call(NONE,lhs,exps,next), SOME extern_pc)

              | C0.Simple(C0.Postop(lhs,postop,extern_pc)) =>
                emit (Postop(lhs,postop,next), SOME extern_pc)

              | C0.Simple C0.Noop =>
                emit (Noop next, NONE) 

              | C0.Return(exp, extern_pc) =>
                emit (Return exp, SOME extern_pc)

              | C0.Break(extern_pc) => 
                let 
                  val {break_pc, break_depth, ...} = get_break cfg_state
                  val firstpop = ref NONE
                  val start = emit (Noop(firstpop), SOME extern_pc)
                  val lastpop = pop_a_lot (firstpop, break_depth)
                in 
                  lastpop := SOME break_pc;
                  start
                end

              | C0.Continue(extern_pc) =>
                let 
                  val {continue_pc, break_depth, ...} = get_break cfg_state
                  val firstpop = ref NONE
                  val start = emit (Noop(firstpop), SOME extern_pc)
                  val lastpop = pop_a_lot (firstpop, break_depth)
                in 
                  lastpop := SOME continue_pc;
                  start
                end

              | C0.If(test, extern_pc, stmtT, stmtF) =>
                let
                  val join_node = emit (Noop next, NONE)
                  val nextT = ref NONE
                  val nextF = ref NONE
                  val test_node 
                    = emit (Test(test, nextT, nextF), SOME extern_pc)
                  val endT = process (nextT, stmtT) cfg_state
                  val endF = 
                      case stmtF of 
                        NONE => nextF
                      | SOME stmtF => process (nextF, stmtF) cfg_state
                in
                  endT := SOME join_node;
                  endF := SOME join_node;
                  test_node 
                end

              | C0.While(test, extern_pc, stmt) => 
                let
                  val exit = emit (Noop next, NONE)
                  val enter = ref NONE
                  val test = 
                    emit (Test(test, enter, ref (SOME exit)), SOME extern_pc)
                  val cfg_state = push_loop cfg_state (exit, test)
                  val finish = process (enter, stmt) cfg_state
                in
                  finish := SOME test;
                  test
                end

              | C0.For(init, test, post, body) => raise Match

              | C0.Compound(body) => 
                let
                  val start = ref NONE
                  val push_node = emit (PushScope start, NONE)
                  val cfg_state = push_scope cfg_state
                  val finish = process_list (start, body) cfg_state
                  val pop_node = emit (PopScope next, NONE)
                in
                  finish := SOME pop_node;
                  push_node 
                end

        in
          parent_next := SOME intern_pc;
          next
        end

      (* Create a fake entry point to push the initial scope. *)
      val start_pc : intern_pc option ref = ref NONE
      val entry_pc : intern_pc = emit (PushScope(start_pc), NONE)
                                 
      (* Create the body of the function. *)
      val end_pc : intern_pc option ref = process_list (start_pc, stmts) X

      (* Create a fake exit point in case there's no return statement. *)
      val exit_pc : intern_pc = emit (Return NONE, NONE)
      val () = end_pc := SOME exit_pc

    in Array.vector (GA.finalize nodes) end

  fun process_graph (nodes : proto_graph) : CFG.graph = 
    let
      fun folder (intern_pc, (node, extern_pc), (extern_to_pc, pc_to_extern)) =
        case extern_pc of
          NONE => (extern_to_pc, pc_to_extern)
        | SOME extern_pc => 
          (MapI.insert (extern_to_pc, extern_pc, intern_pc),
           MapI.insert (pc_to_extern, intern_pc, extern_pc))
      val (extern_to_pc, pc_to_extern)
        = Vector.foldri folder (MapI.empty, MapI.empty) nodes
      fun mapper (ref NONE) = raise GraphConstruction
        | mapper (ref (SOME intern_pc)) = intern_pc
    in
      {entry_point = 0, (* DANGER? *)
       nodes = Vector.map (map mapper o #1) nodes,
       extern_to_pc = extern_to_pc,
       pc_to_extern = pc_to_extern}
    end

  val mkgraph = process_graph o build_graph

  fun mkprog_folder (decl, prog as {functions, ty_vars, struct_defs}) =
    case decl of
      C0.DeclStructDecl _ => prog
    | C0.DeclStructDef (s, fields) => 
      let in
        {functions = functions,
         ty_vars = ty_vars,
         struct_defs = MapS.insert (struct_defs, s, fields)}
      end
    | C0.DeclTypeDefTy (ty, t) => 
      let in
        {functions = functions,
         ty_vars = MapS.insert (ty_vars, t, ty),
         struct_defs = struct_defs}
      end
    | C0.DeclExternFun _ => prog
    | C0.DeclFunDecl _ => prog
    | C0.DeclFunDef ((ty, f, args), stmts) => 
      let 
        val function = {return_type = ty, args = args, graph = mkgraph stmts}
      in
        {functions = MapS.insert (functions, f, function),
         ty_vars = ty_vars, 
         struct_defs = struct_defs}
      end

  val mkprog : C0.program -> CFG.program = 
      foldr mkprog_folder 
        {functions = MapS.empty, 
         ty_vars = MapS.empty, 
         struct_defs = MapS.empty}
end
