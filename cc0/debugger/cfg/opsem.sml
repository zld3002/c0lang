(*
structure CState = 
State(structure Data = ConcreteData
      val allow_unitialized_stack_variables = true)

structure CEval = 
Cymbol(structure Data = ConcreteData structure State = CState)
*)

functor OpSemFn (structure Data : CONCRETE_DATA 
                 structure State : CONCRETE_STATE
                 structure Call : CALL 
                    where type value = State.value 
                      and type 'a state = 'a State.state) :> 
        OP_SEM where type state = (C0.var_name * 
                                   CFG.pc * 
                                   (CFG.pc -> CFG.pc CFG.node)) State.state 
                 and type value = State.value =
struct

  structure Eval =
  EvalFn (structure Data = Data
          structure State = State)

  (* Keep an eye on what is going on *)
  val print_st = fn NONE => () | SOME p => print ("Pos: " ^ Mark.show p ^ "\n")
  val print_locals = State.print_locals

  val print = fn _ => ()
  val print_st = fn _ => ()
  val print_locals = fn _ => ()

  type value = State.value
  type state =
       (C0.var_name * 
        CFG.pc * 
        (CFG.pc -> CFG.pc CFG.node)) State.state
  type position = (CFG.pc -> CFG.pc CFG.node) * CFG.pc CFG.node

  exception Done of state * State.value

  fun step prog state (graph, node : CFG.pc CFG.node) = 
    let in
      case node of
        CFG.Stmt (stmt, pos, next) => 
        let in 
          print_st pos;
          print "Simple statement\n";
          ignore (Eval.eval_simp (state, stmt));
          (graph, graph next)
        end
        
      | CFG.PushScope next => 
        let in
          print "Push scope\n";
          State.push_scope state;
          (graph, graph next)
        end
                              
      | CFG.PopScope (next, n) => 
        let in
          print "Before pop scope\n";
          print_locals state;
          print "After pop scope\n";
          State.pop_scope (state, n);
          print_locals state;
          (graph, graph next)
        end

      | CFG.Declare (ty, x, next) =>
        let in
          State.declare (state, x, ty);
          (graph, graph next)
        end
                             
      | CFG.Test (test, pos, nextT, nextF) => 
        let
          val cond = State.to_bool (Eval.eval_exp (state, test)) 
        in
          print_st pos;
          print "Test\n";
          (graph, graph (if cond then nextT else nextF))
        end
        
      | CFG.Return (exp, pos) => 
        let val v =
              case exp of 
                NONE => State.unit 
              | SOME exp => Eval.eval_exp (state, exp)
        in
          print "Return\n";
          case State.pop_fun (state) of
            NONE => raise Done (state, v)
          | SOME (f, (x, pc, graph)) =>
            let in
              State.put_id (state, x, v);
              (graph, graph pc)
            end
        end
        
      | CFG.Assert (e1, e2, pos, next) => 
        let 
          val cond = State.to_bool   (Eval.eval_exp (state, e1))
          val msg  = State.to_string (Eval.eval_exp (state, e2))
        in 
          if cond then (graph, graph next) 
          else raise Error.AssertionFailed msg
        end

      | CFG.Call (x, e, es, pos, next) => 
        let 
          val f = State.to_function (Eval.eval_exp (state, e))
          val vs = Eval.eval_exps (state, es)
          val func = 
              case CFG.functions prog f of
                NONE => raise Error.Dynamic ("no function " ^ f)
              | SOME func => func
          val return_ty = CFG.return_ty func
          val arg_tys = CFG.arg_tys func
          val () = State.push_scope state
          val () = State.declare (state, x, return_ty)
        in          
          if length arg_tys = length vs then ()
          else raise Error.Dynamic ("Wrong number of arguments to " ^ f);
          if CFG.internal_function func
          then (* Handle internal function *)
            let 
              val targs = ListPair.zip (CFG.args func, vs)
              val new_graph = CFG.graph func
              fun init_arg ((ty, x), v) = 
                  let in
                    print ("Declaring " ^ C0.id_string x ^ "\n");
                    State.declare (state, x, ty); 
                    State.put_id (state, x, v)
                  end
            in 
              State.push_fun (state, f, (x, next, graph));
              app init_arg targs;
              (new_graph, CFG.entry_point func)
            end 
          else (* Handle external function *)
            let
              val targs = ListPair.zip (arg_tys, vs)
              val v = 
                    Call.call_external
                        (state, CFG.library func, f, return_ty, targs)
            in 
              State.put_id (state, x, v);
              (graph, graph next)
            end
        end
    end
      
  fun run (prog, n) = 
    let
       val main = 
          case (CFG.functions prog "main") of
                   NONE => raise Error.Dynamic ("no main function to run")
                 | SOME main => main

      val state = 
          State.new_state 
              {ty_vars = CFG.ty_vars prog, 
               st_defs = CFG.struct_defs prog, 
               fun_defs = CFG.fun_defs prog,
               initial_function = "__init__"}

      fun loop m x = 
          if m = n then ()
          else loop (m + 1) (step prog state x)

    in 
      (loop 0 CFG.launcher; NONE)
      handle Done (_, result) => SOME (State.to_int result)
    end

 
(*
  fun eval prog x = 
    let 
      val prog = CFG.functions prog
      fun loop x = loop (step prog x)
    in
      loop x handle Done y => y
    end

  exception Timeout

*)

end


