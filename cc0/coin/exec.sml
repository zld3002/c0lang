structure Exec:> EXEC =
struct

structure State = ConcreteState
structure C0 = C0Internal

datatype call_info = 
   Native of State.value 
 | Interp of CodeTab.fun_ty * C0Internal.program 

datatype step_info = 
   ReturnNone 
 | ReturnSome of State.value 
 | PC of int


val current_pos: Mark.ext option ref = ref NONE

val current_depth = ref 0

val lookup_fun = 
 fn x =>
    case Symtab.lookup x of
       SOME (Ast.Function (_, tp, args, _, _, _, _)) =>
       SOME (tp, map (fn Ast.VarDecl (_, tp, _, _) => tp) args)
     | _ => NONE

val lookup_struct = 
fn x =>
    case Structtab.lookup x of
       SOME (Ast.Struct (_, SOME flds, _, _)) => 
       SOME (map (fn Ast.Field (field, fieldty, _) => (fieldty, field)) flds)
     | _ => NONE

val lookup_type =
 fn x =>
    case Symtab.lookup x of 
       SOME (Ast.TypeDef (_, tp, _)) => SOME tp
     | _ => NONE

val state : (Symbol.symbol * Mark.ext) State.state = 
   State.new_state 
      {lookup_fun = lookup_fun,
       lookup_struct = lookup_struct,
       lookup_type = lookup_type,
       initial_function = Symbol.symbol "__init__"}

val lastval : State.value ref = ref State.unit

fun last () = !lastval

fun print_locals () = State.print_locals state

fun print_fun n (called_fun_name, (fun_name, pos)) =
 ( print ("               "^Symbol.name fun_name^" from "^Mark.show pos^"\n")
 ; if n = 0 
      then () 
   else print ("                  (and "^Int.toString n^" similar)\n"))

fun print_ps (n, (f1, p1) :: (f2, p2) :: funs) =
      (if Symbol.compare (f1, f2) = EQUAL andalso #2 p1 = #2 p2
          then print_ps (n+1, (f2, p2) :: funs)
       else (print_fun n (f1, p1); print_ps (0, (f2, p2) :: funs)))
  | print_ps (n, [ f ]) = print_fun n f
  | print_ps (_, []) = ()

fun print_trace ps = 
 ( case !current_pos of 
      NONE => ()
    | SOME pos => print ("Last position: "^Mark.show pos^"\n")
 ; print_ps (0, rev ps))

fun print_result (exp, v) =
let 
   fun identifier () = 
      case exp of 
         NONE => ""
       | SOME x => C0.expToString false x^" is " 
in
   if Flag.isset Flags.flag_trace andalso (not (State.is_unit v))
      then print (identifier ()^State.value_string v^"\n")
   else ()
end

fun reset () = 
 ( print_trace (State.stacktrace state)
 ; current_depth := 0
 ; current_pos := NONE)


(* Return code to interpret, or execute native call *)
fun call_step (fun_name, actual_args, pos) : call_info = 
  (case CodeTab.lookup fun_name of
      NONE => raise Error.Internal ("Undefined fun "^Symbol.name fun_name)
    | SOME (CodeTab.AbsentNative (_, lib)) =>
         raise Error.Dynamic ("Function "^Symbol.name fun_name^
                              ", defined in library <"^lib^
                              ">, did not load correctly")
    | SOME (CodeTab.Interpreted (f_ty, code)) => 
         Interp (f_ty, code)
    | SOME (CodeTab.Native ((return_ty, arg_tys), fptr)) => 
      let 
         val fnative = Symbol.symbol (Symbol.name fun_name ^ " (native)") 
         val () = Flag.guard Flags.flag_trace
                     (fn () => print ("Calling native "^Symbol.name fun_name^
                                      "\n"))
                     ()
         val () = State.push_fun (state, fnative, (fnative, pos))
         val old_pos = !current_pos
         val () = current_pos := SOME ((0,0),(0,0),"< in native code >")
         val args = ListPair.zip (map #1 arg_tys, actual_args)
         val res = Calling.call state (fptr, return_ty, args)
      in 
       ( Flag.guard Flags.flag_trace
            (fn () => print ("Done with native "^Symbol.name fun_name^"\n"))
            ()
       ; ignore (State.pop_fun state)
       ; current_pos := old_pos 
       ; Native(res))
      end)


(* Execute a hunk of bytecode *)
fun exec program: State.value = 
let
   fun run pc = 
   let
      val _ =  
         Flag.guard Flags.flag_trace
            (fn () => print ("Location "^Int.toString pc^", stack depth "^ 
                             Int.toString (!current_depth)^"\n"))
            ()
   in case step (program, pc) of
         ReturnNone => State.unit
       | ReturnSome res => res
       | PC i => run i
   end
in 
   run 0 before current_pos := NONE 
end


(* Call a function with some values *)
and call (fun_name, actual_args, pos): State.value = 
let
   val old_depth = !current_depth
   val f = Symbol.name fun_name
   val () = current_depth := 0
   val () = current_pos := SOME pos
in
   case call_step (fun_name, actual_args, pos) of
      Native res => res
    | Interp ((_, formal_args), code) => 
       ( State.push_fun (state, fun_name, (fun_name, pos))
       ; app (fn ((tp, x), v) => 
               ( State.declare (state, x, tp)
               ; State.put_id (state, x, v)))
            (ListPair.zip (formal_args, actual_args))
       ; Flag.guard Flags.flag_trace
            (fn () => print ("Starting execution of "^f^"\n")) 
            ()
       ; exec code
         before
          ( ignore (State.pop_fun state)
          ; Flag.guard Flags.flag_trace
               (fn () => print ("Ending execution of "^f^"\n")) 
               ()))
   before current_depth := old_depth
end


(* Execute a single bytecode command *)
and step ((cmds, labs), pc): step_info =
let
in 
   case (Vector.sub (cmds,pc)) of
      C0.Label _ => PC(pc+1)

    | C0.Exp (e, pos) =>
      let 
         val () = current_pos := SOME pos
         val v = Eval.eval_exp state e
      in
       ( print_result (NONE, v)
       ; lastval := v
       ; PC (pc+1))
      end

    | C0.CCall (x, f, args, pos) =>
      let
         val actual_args = List.map (Eval.eval_exp state) args
         val v = call (f, actual_args, pos)
      in 
       ( print_result (Option.map C0.Var x, v)
       ; lastval := v
       ; case x of 
            NONE => ()
          | SOME x => State.put_id (state, x, v)
       ; PC (pc+1))
      end

    | C0.Declare (tp, x, NONE) => 
       ( State.declare (state, x, tp)
       ; PC (pc+1))

    | C0.Declare (tp, x, SOME (e, pos)) => 
      let
         val () = current_pos := SOME pos
         val v = Eval.eval_exp state e
      in
       ( State.declare (state, x, tp)
       ; State.put_id (state, x, v) 
       ; print_result (SOME (C0.Var x), v) 
       ; lastval := v
       ; PC (pc+1))
      end

    (* Address-of operation; introduced as part of isolation *)
    | C0.Assign (SOME(C0.Addr),e1,e2,pos) =>
      let
         val () = current_pos := SOME pos
         val l_loc = Eval.eval_lval state e1

         (* Evaluate the righthand side of the assignment to a location.
          * The location should always be a heap address *)
         val r_loc as (tp,addr) = 
            case Eval.eval_lval state e2 of
               Eval.HeapLoc (tp, addr) => (tp, addr)
             | _ => raise Error.Internal "Addr of operation on a non-heap \
                                         \location\n"

         (* Here lies the terrible hack. *)
         val v = State.pointer (tp,addr)
      in
       ( Eval.put (state, l_loc, v)
       ; print_result (SOME e1, v)
       ; lastval := v
       ; PC (pc+1))
      end

    | C0.Assign (oper, e1, e2, pos) => 
      let 
         val () = current_pos := SOME pos
         val loc = Eval.eval_lval state e1
         val v = Eval.eval_exp state e2
         val v' =
            case oper of
                      NONE => v
                    | SOME oper => 
                      Eval.eval_binop oper (Eval.get (state, loc), v)
      in 
       ( Eval.put (state, loc, v')
       ; print_result (NONE, v)
       ; lastval := v'
       ; PC (pc+1))
      end

    | C0.Assert (e, msg, pos) => 
       ( current_pos := SOME pos
       ; if State.to_bool (Eval.eval_exp state e) 
            then () 
         else raise Error.AssertionFailed msg
       ; PC (pc+1))

    | C0.CondJump (e, pos, altlab) =>
       ( current_pos := SOME pos
       ; if (State.to_bool (Eval.eval_exp state e))
            then PC (pc+1)
         else PC(Vector.sub (labs, altlab)+1))

    | C0.Jump labl => PC(Vector.sub (labs, labl))

    | C0.Return NONE => ReturnNone

    | C0.Return (SOME (e, pos)) =>
       ( current_pos := SOME pos
       ; ReturnSome(Eval.eval_exp state e))

    | C0.PushScope => 
       ( current_depth := !current_depth + 1
       ; State.push_scope state
       ; PC(pc+1))

    | C0.PopScope n => 
       ( current_depth := !current_depth - n
       ; State.pop_scope (state, n)
       ; PC(pc+1))
end

end
