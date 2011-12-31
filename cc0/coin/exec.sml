structure Exec = 
struct

structure State = ConcreteState
structure C0 = C0Internal

val current_pos : Mark.ext option ref = ref NONE
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

fun print_fun n (called_fun_name, (fun_name, pos)) =
    (print ("               " ^ Symbol.name fun_name ^ " from "
            ^ Mark.show pos ^ "\n")
     ; if n = 0 then () 
       else print ("                  (and " ^ Int.toString n ^ " similar)\n"))
fun print_ps (n, (f1, p1) :: (f2, p2) :: funs) =
    if Symbol.compare (f1, f2) = EQUAL andalso #2 p1 = #2 p2
    then print_ps (n+1, (f2, p2) :: funs)
    else (print_fun n (f1, p1); print_ps (0, (f2, p2) :: funs))
  | print_ps (n, [ f ]) = print_fun n f
  | print_ps (_, []) = ()
fun print_trace ps = 
    (case !current_pos of 
        NONE => ()
      | SOME pos => print ("Last position: " ^ Mark.show pos ^ "\n")
     ; print_ps (0, rev ps))
fun reset () = 
  (print_trace (State.stacktrace state)
   ; current_depth := 0
   ; current_pos := NONE)

fun call (fun_name, actual_args, pos) : State.value = 
   let 
      val old_depth = !current_depth 
      val () = current_depth := 0
      val f = Symbol.name fun_name
   in
     (case CodeTab.lookup fun_name of
         NONE => raise Error.Internal ("Undefined fun " ^ f)
       | SOME (CodeTab.AbsentNative (_, lib)) =>
         raise Error.Dynamic ("Function " ^ f 
                              ^ ", defined in library <" ^ lib
                              ^ ">, did not load correctly")
       | SOME (CodeTab.Native ((return_ty, arg_tys), fptr)) =>
         let 
            val fnative = Symbol.symbol (f ^ " (native)") 
            val () = Flag.guard Flags.flag_trace
                        (fn () => print ("Calling native " ^ f ^ "\n")) ()
            val () = State.push_fun (state, fnative, (fnative, pos))
            val old_pos = !current_pos
            val () = current_pos := SOME ((0,0),(0,0),"< in native code >")
            val args = ListPair.zip (map #1 arg_tys, actual_args)
            val res = Calling.call (fptr, return_ty, args)
        in 
            Flag.guard Flags.flag_trace
               (fn () => print ("Done with native " ^ f ^ "\n")) ()
            ; ignore (State.pop_fun state)
            ; current_pos := old_pos 
            ; res 
         end
       | SOME (CodeTab.Interpreted ((_, formal_args), code)) =>
         (State.push_fun (state, fun_name, (fun_name, pos))
          ; current_pos := SOME pos
          ; app (fn ((tp, x), v) => 
                    (State.declare (state, x, tp)
                     ; State.put_id (state, x, v)))
                (ListPair.zip (formal_args, actual_args))
          ; Flag.guard Flags.flag_trace
               (fn () => print ("Starting execution of " ^ f ^ "\n")) ()
          ; let val v = case exec code of
                           NONE => State.unit
                         | SOME v => v
            in
               ignore (State.pop_fun state)
               ; Flag.guard Flags.flag_trace
                    (fn () => print ("Ending execution of " ^ f ^ "\n")) ()
               ; v
            end))
      before current_depth := old_depth
   end

and exec (cmds, labs) : State.value option = 
   let
      fun run pc = 
        (Flag.guard Flags.flag_trace
            (fn () => print ("Location " ^ Int.toString pc ^ ", stack depth " 
                             ^ Int.toString (!current_depth) ^ "\n")) ()
         ; arun pc)
      and arun pc = 
         case Vector.sub (cmds, pc) of 
            C0.Label _ => run (pc+1)
          | C0.Exp (e, pos) =>
            let 
               val () = current_pos := SOME pos
               val v = Eval.eval_exp (state, call) e
            in
               if !current_depth = 0 orelse Flag.isset Flags.flag_trace
               then if State.is_unit v then ()
                    else print (State.value_string v ^ "\n")
               else ()
               ; run (pc+1)
            end

          | C0.Declare (tp, x, NONE) => 
            (State.declare (state, x, tp)
             ; run (pc+1))
          | C0.Declare (tp, x, SOME (e, pos)) => 
            let
               val () = current_pos := SOME pos
               val v = Eval.eval_exp (state, call) e
            in
               State.declare (state, x, tp)
               ; State.put_id (state, x, v) 
               ; if !current_depth = 0 orelse Flag.isset Flags.flag_trace 
                 then print (Symbol.name x ^ " is " ^
                             State.value_string v ^ "\n")
                 else ()
               ; run (pc+1)
            end 
          | C0.Assign (oper, e1, e2, pos) => 
            let 
               val () = current_pos := SOME pos
               val loc = Eval.eval_lval (state, call) e1
               val v = Eval.eval_exp (state, call) e2
               val v' =
                  case oper of
                     NONE => v
                   | SOME oper => 
                     Eval.eval_binop oper (Eval.get (state, loc), v)
            in 
               Eval.put (state, loc, v')
               ; if !current_depth = 0 orelse Flag.isset Flags.flag_trace 
                 then print (C0.expToString false e1 ^ " is " ^
                             State.value_string v' ^ "\n")
                 else ()
               ; run (pc+1)
            end
          | C0.Assert (e, msg, pos) => 
            (current_pos := SOME pos
             ; if State.to_bool (Eval.eval_exp (state, call) e) then () 
               else raise Error.AssertionFailed msg
             ; run (pc+1))
          | C0.CondJump (e, pos, altlab) =>
            (current_pos := SOME pos
             ; if (State.to_bool (Eval.eval_exp (state, call) e))
               then run (pc+1)
               else run (Vector.sub (labs, altlab)+1))
          | C0.Jump labl => run (Vector.sub (labs, labl))
          | C0.Return NONE => NONE
          | C0.Return (SOME (e, pos)) =>
            (current_pos := SOME pos
             ; SOME (Eval.eval_exp (state, call) e))
          | C0.PushScope => 
            (current_depth := !current_depth + 1
             ; State.push_scope state
             ; run (pc+1))
          | C0.PopScope n => 
            (current_depth := !current_depth - n
             ; State.pop_scope (state, n)
             ; run (pc+1))
   in 
      run 0 before current_pos := NONE 
   end

end
