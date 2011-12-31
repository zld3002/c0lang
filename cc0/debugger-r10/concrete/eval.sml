structure State = State(Concrete)

structure EvalExp = Cymbol(structure Data = Concrete structure State = State)

signature EVAL = sig

  datatype pc 
    = Step    of CFG.intern_pc
    | StepIn  of string * State.value list
    | StepOut of string * CFG.intern_pc

  datatype next = More of pc | Done of State.value option

  type state = (EvalExp.loc option * CFG.intern_pc) State.state

  val start : CFG.program -> string -> state * pc
  val eval : state * CFG.intern_pc CFG.node -> state * next
  val run : CFG.program -> Word32.word

end

structure Eval (* :> EVAL *) = struct

  open State
  open EvalExp
  type state = (EvalExp.loc option * CFG.intern_pc) State.state

  datatype pc 
    = Step    of CFG.intern_pc
    | StepIn  of string * State.value list
    | StepOut of string * CFG.intern_pc

  datatype next = More of pc | Done of State.value option

  fun eval (state, node : CFG.intern_pc CFG.node) = 
    case node of
      CFG.Decl (ty,x,NONE,next) => (declare (state, ty, x), More (Step next))
    | CFG.Decl (ty,x,SOME exp,next) => 
      let
        val state = declare (state, ty, x)
        val (state, v) = eval_exp (state, exp)
      in (put_id (state, x, v), More (Step next)) end

    | CFG.Assign (lhs,oper,exp,next) => 
      let 
        val (state, loc) = eval_lval (state, lhs)
        val v1 = get(state, loc)
        val (state, v2) = eval_exp (state, exp)
      in 
        case oper of 
          NONE => (put(state,loc,v2), More (Step next))
        | SOME oper => 
          (put(state,loc,eval_binop oper (v1,v2)), More (Step next))
      end

    | CFG.Call (lhsx,lhsf,exps,next) => 
      let 
        (* Evaluate left-hand side to a location (maybe) *)
        val (state, locx) = 
            case lhsx of 
              NONE => (state, NONE)
            | SOME lhsx => 
              let val (state, loc) = eval_lval (state, lhsx) 
              in (state, SOME loc) end

        (* Get the function *)
        val (state, locf) = eval_lval (state, lhsf) 
        val f = to_function (get (state, locf)) 

        (* Evaluate function arguments in left-to-right order *)
        val (state, vs) = eval_exps (state, exps)

      in (push_fun (state, f, (locx, next)), More (StepIn (f, vs))) end

    | CFG.Postop (lhs,oper,next) => 
      let 
        val (state, addr) = eval_lval (state, lhs) 
        val v = State.to_int (get (state, addr))
      in
        (put (state, addr, 
              State.int(case oper of 
                          C0.Inc => Concrete.int_add(v, Word32.fromInt 1) 
                        | C0.Dec => Concrete.int_sub(v, Word32.fromInt 1))),
         More (Step next))
      end

    | CFG.Noop next => (state, More (Step next))
    | CFG.PushScope next => (push_scope state, More (Step next))
    | CFG.PopScope next => (pop_scope state, More (Step next))
    | CFG.Test (test,nextT,nextF) => 
      let
        val (state, v) = eval_exp (state, test)
      in (state, More (Step (if to_bool v then nextT else nextF))) end

    | CFG.Return exp => 
      let
        val (state, v) =
          case exp of
            NONE => (state, NONE)
          | SOME exp => 
            let val (state, v) = eval_exp (state, exp) in (state, SOME v) end
      in
        case pop_fun state of
          NONE => (state, Done v)
        | SOME (state, f, (loc, pc)) =>
          (case (loc, v) of
             (NONE, _) => (state, More (StepOut (f, pc)))
           | (SOME loc, SOME v) => (put(state, loc, v), More (StepOut (f, pc)))
           | _ => raise Error.Dynamic "value was expected; none was returned")
      end

  fun eval_step_in (prog : CFG.program) (state, (f, args)) = 
    let 
      val func = MapS.lookup (#functions prog, f) 
      val args = ListPair.zip(#args func, args)
      fun folder (((ty,x),v), state) = 
          put (declare(state, ty, x), StackLoc x, v) 
      val nodes = #nodes (#graph func)
      val entry_point = #entry_point (#graph func)    
    in (foldr folder state args, func) end
      
  fun start (prog : CFG.program) s = 
    let in
      (State.new_state {ty_vars = #ty_vars prog, 
                        struct_defs = #struct_defs prog, 
                        initial_function = s},
       Step (#entry_point (#graph (MapS.lookup (#functions prog, s)))))
    end

  fun step (prog, graph, state, pc) = 
    case pc of 
      Step next => 
      let in
        (* print ("At function " ^ current_function state ^ 
                  ", pc " ^ Int.toString next ^ "\n"); 
        print_state state; *)
        (prog, graph, (eval(state, Vector.sub(#nodes graph, next))))
      end
      
    | StepIn next =>
      let 
        val (state, func) = eval_step_in prog (state, next)
        val graph = #graph func
        val entry_point = #entry_point (#graph func)
      in 
        (* print ("Entering " ^ current_function state ^ "\n"); *)
        (prog, graph, (state, More (Step entry_point)))
      end
      
    | StepOut (f, resume_point) => 
      let 
        val func = MapS.lookup (#functions prog, f)
        val graph = #graph func
      in 
        (* print ("Returning to " ^ current_function state ^ "\n"); *)
        (prog, graph, (state, More (Step resume_point)))
      end
      
  fun go x = 
    case step x of 
      (prog, nodes, (state, Done v)) => (state, v)
    | (prog, nodes, (state, More pc)) => go (prog, nodes, state, pc)

  (* Evaluates a series of arguments to completion on a fresh stack *)
  fun magicfun prog (original_state, f, args) = 
    let
      val func = MapS.lookup (#functions prog, f) 
      val args = ListPair.zip(#args func, args)
      fun folder (((ty,x),v), state) = 
          put (declare(state, ty, x), StackLoc x, v)
      val (state, entry_point) = start prog f 
      val state = foldr folder state args
      val state = put_heap (state, get_heap original_state)
      val (state, v) = go (prog, #graph func, state, entry_point)
    in (put_heap (original_state, (get_heap state)), v) end

  fun run (prog : CFG.prog) = 
    let
      val main_graph = #graph (MapS.lookup (#functions prog, "main"))
      val (state, entry_point) = start prog "main"
      val state = CState.put_magicfun (state, magicfun prog)
    in 
      to_int (valOf (#2 (go (prog, main_graph, state, entry_point))))
    end

end

