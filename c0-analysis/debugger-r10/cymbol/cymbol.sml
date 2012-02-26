(* Dynamic semantics for expressions and lvalues *)
(* Robert J. Simmons                             *)

signature CYMBOL = sig

  type 'a state
  type addr
  type value

  datatype loc = StackLoc of C0.variable_name | HeapLoc of addr
  val get : 'a state * loc -> value
  val put : 'a state * loc * value -> 'a state

  val eval_exp   : 'a state * C0.exp -> 'a state * value
  val eval_exps  : 'a state * C0.exp list -> 'a state * value list
  val eval_lval  : 'a state * C0.exp -> 'a state * loc
  val eval_binop : C0.binop -> value * value -> value

end

functor Cymbol (structure Data : DATA
                structure State : 
                          STATE where type boolrep = Data.boolrep 
                                and type intrep = Data.intrep) 
        :> CYMBOL where type value = State.value
                  and type addr = State.addr
                  and type 'a state = 'a State.state = struct

  (* Satisfy functor specification *)  
  open State

  (* Datatypes and exceptions *)

  datatype loc = StackLoc of C0.variable_name | HeapLoc of addr

  fun get (state, StackLoc x) = get_id (state, x)
    | get (state, HeapLoc addr) = get_addr (state, addr)

  fun put (state, StackLoc x, v) = put_id (state, x, v)
    | put (state, HeapLoc addr, v) = put_addr (state, addr, v)

  (* Evaluation *)
  fun eval_const c = 
    case c of
      C0.Bool b => bool (Data.from_bool b)
    | C0.Int i => int (Data.from_int i)
    | C0.Char c => char c
    | C0.String s => string s
    | C0.NullPointer => null

  fun zip (f,g) (x,y) = (f x, g y)

  fun eval_monop monop = 
    case monop of 
      C0.LogicNot => bool o Data.bool_not o to_bool
    | C0.ArithNeg => int o Data.int_not o to_int
    | C0.BitNot   => int o Data.bit_not o to_int
     
  fun eval_binop binop = 
    case binop of
      C0.Plus       => int  o Data.int_add    o zip(to_int,to_int)
    | C0.Times      => int  o Data.int_mul    o zip(to_int,to_int)
    | C0.Minus      => int  o Data.int_sub    o zip(to_int,to_int)
    | C0.Div        => int  o Data.int_div    o zip(to_int,to_int)
    | C0.Mod        => int  o Data.int_mod    o zip(to_int,to_int)
    | C0.BitAnd     => int  o Data.int_bitand o zip(to_int,to_int)
    | C0.BitOr      => int  o Data.int_bitor  o zip(to_int,to_int)
    | C0.BitXor     => int  o Data.int_bitxor o zip(to_int,to_int)
    | C0.ShiftLeft  => int  o Data.int_shiftl o zip(to_int,to_int)
    | C0.ShiftRight => int  o Data.int_shiftr o zip(to_int,to_int)
    | C0.Lt         => bool o Data.int_lt     o zip(to_int,to_int)
    | C0.Leq        => bool o Data.int_leq    o zip(to_int,to_int)
    | C0.Geq        => bool o Data.int_geq    o zip(to_int,to_int)
    | C0.Gt         => bool o Data.int_gt     o zip(to_int,to_int)
    | C0.LogicAnd   => bool o Data.bool_and   o zip(to_bool,to_bool)
    | C0.LogicOr    => bool o Data.bool_or    o zip(to_bool,to_bool)
    | C0.Eq         => bool o value_eq
    | C0.Neq        => bool o value_neq

  fun to_heap loc = 
    case loc of
      StackLoc _ => 
      raise Error.Dynamic "stack location given; heap location is required"
    | HeapLoc addr => addr

  fun eval_lval (state, exp) = 
    case exp of 
      C0.Var x => (state, StackLoc x)
    | C0.Ref exp => 
      let val (state, v) = eval_exp (state, exp)
      in (state, HeapLoc (to_addr v)) end
    | C0.Index (exp, expi) =>
      let
        val (state, vaddr) = eval_exp (state, exp)
        val (state, v) = eval_exp (state, expi)
      in (state, HeapLoc (offset_index (to_addr vaddr, to_int v))) end
    | C0.RefField (exp, f) => 
      let val (state, v) = eval_exp (state, exp)
      in (state, HeapLoc (offset_field (to_addr v, f))) end
    | C0.Field (exp, f) => 
      let
        val (state, loc : loc) = eval_lval (state, exp)
      in (state, HeapLoc (offset_field (to_heap loc, f))) end
    | C0.Ternary (exp, expT, expF) => 
      let val (state, v) = eval_exp (state, exp) in
        if Data.to_bool (to_bool v)
        then eval_lval (state, expT) else eval_lval (state, expF)
      end
    | _ => raise Error.Dynamic "invalid lvalue"

  and eval_exps (state, exps) =
    let 
      fun evals (state, [], vs) = (state, rev vs)
        | evals (state, exp :: exps, vs) = 
          let val (state, v) = eval_exp (state, exp) 
          in evals (state, exps, v :: vs) end
    in evals (state, exps, []) end

  and eval_exp (state, exp) = 
    case exp of
    (* Constants and variables *)
      C0.Const c => (state, eval_const c)
    | C0.Var x => (state, get_id (state, x))

    (* Primitive operations, including short-circuting logic operations *)
    | C0.Binop (exp1, C0.LogicAnd, exp2) =>
      let val (state, v1) = eval_exp (state, exp1) in 
        if Data.to_bool (to_bool v1)
        then eval_exp (state, exp2) else (state, bool (Data.from_bool false))
      end
    | C0.Binop (exp1, C0.LogicOr, exp2) =>
      let val (state, v1) = eval_exp (state, exp1) in
        if Data.to_bool (to_bool v1) 
        then (state, bool (Data.from_bool true)) else eval_exp (state, exp2)
      end
    | C0.Binop (exp1, oper, exp2) =>
      let 
        val (state, v1) = eval_exp (state, exp1)
        val (state, v2) = eval_exp (state, exp2)
      in (state, eval_binop oper (v1, v2)) end
    | C0.Monop (oper, exp) =>
      let
        val (state, v) = eval_exp (state, exp) 
      in (state, eval_monop oper v) end
    | C0.Ternary (exp, expT, expF) =>
      let val (state, v) = eval_exp (state, exp) in
        if Data.to_bool (to_bool v)
        then eval_exp (state, expT) else eval_exp (state, expF)
      end

    (* State allocation *)
    | C0.Alloc(ty) => alloc(state, ty)

    | C0.AllocArray(ty, exp) => 
      let 
        val (state, v) = eval_exp (state, exp) 
      in alloc_array (state, ty, to_int v) end

    (* State access *)
    | C0.Ref exp =>
      let 
        val (state, v) = eval_exp (state, exp)
      in (state, get_addr (state, to_addr v)) end
    | C0.Index (exp, expi) =>
      let
        val (state, vaddr) = eval_exp (state, exp)
        val (state, v) = eval_exp (state, expi)
      in (state, get_addr (state, offset_index (to_addr vaddr, to_int v))) end
    | C0.RefField (exp, f) => 
      let val (state, v) = eval_exp (state, exp)
      in (state, get_addr (state, offset_field (to_addr v, f))) end
    | C0.Field (exp, f) => 
      let
        val (state, loc : loc) = eval_lval (state, exp)
      in (state, get_addr (state, offset_field (to_heap loc, f))) end

    (* Functions *)
    | C0.Call(C0.Func(exp, exps, _)) => 
      let 
        val (state, loc) = eval_lval (state, exp)
        val f = to_function (get (state, loc))
        val (state, vs) = eval_exps (state, exps)
        val (state, res) = get_magicfun state (state, f, vs)
      in (state, case res of NONE => unit | SOME v => v) end

(*
  val pointer = fn Pointer x => x | _ => raise TypeCast
  val Cell_val    = fn v => Cell (MapS.singleton ("",v))
  val Cell_struct = fn vs => Cell vs
  val cell_val = fn Cell (vs) => (case MapS.find (vs, "") of
                                    NONE => Uninitalized
                                  | SOME v => v)
                  | _ => raise TypeCast
  val cell_struct = fn Cell vs => vs | _ => raise TypeCast
  val array = fn Array a => a | _ => raise TypeCast   

  datatype 'a stack
    = T of {stack  : value MapX.map list, 
            caller : ('a * 'a stack) option}
      
  datatype 'a state
    = S of {heap   : mem MapI.map, 
            stack  : 'a stack}

  fun str_value v = 
    case v of
      Int i        => ("Int:        " ^ Data.int_to_string i)
    | Bool b       => ("Bool:       " ^ Data.bool_to_string b)
    | String s     => ("String:     \"" ^ s ^ "\"") 
    | Pointer 0    => ("Null pointer")
    | Pointer l    => ("Pointer to: " ^ Int.toString l)
    | Uninitalized => ("Uninitialized")
    | Nothing      => ("Invalid")

  fun str_stack stack =
      String.concat
          (map (fn (C0.Normal x, v) => x ^ " --> " ^ str_value v ^ "\n") 
               (MapX.listItemsi stack))

  fun print_mem (i,mem) = 
    case mem of 
      Cell vs =>
      let in
        case MapS.find (vs, "") of 
          NONE =>
          if MapS.isEmpty vs 
          then print (Int.toString i ^ " --> Uninitialized\n")
          else print (Int.toString i ^ " --> { # STRUCT }\n")
        | SOME v => print (Int.toString i ^ " --> " ^ str_value v ^ "\n") 
      end
    | Array _  => print (Int.toString i ^ " --> { # ARRAY }\n")


  fun print_state (S{heap, stack = T{stack, caller}}) = 
    let in
      print "------------\n";
      print "-- Stack: --\n";
      print "------------\n";
      print (String.concatWith "----------\n" (map str_stack stack));
      print "------------\n";
      print "-- Heap: ---\n";
      print "------------\n";
      MapI.appi print_mem heap;
      print "------------\n"
    end    
    

  datatype addr 
    = Stack of C0.ident
    | Heap  of int
    | Index of int * int 
    | Field of int * string

  fun offset_index (addr, i) = 
    case addr of Heap l => Index (l, i) | _ => raise CymbolError "Bad offset"
  fun offset_field (addr, x) = 
    case addr of Heap l => Field (l, x) | _ => raise CymbolError "Bad offset"

  (* STATE MODIFICATION FUNCTIONS *)
  fun get_stack ([], x) = raise CymbolError "Non-existant variable"
    | get_stack (map :: maps, x) = 
      case MapX.find (map, x) of
        NONE => get_stack (maps, x)
      | SOME v => v

  fun get (S{heap, stack = T{stack, caller}}, addr) =
    case addr of
      Stack x => get_stack (stack, x)
    | Heap l => cell_val (MapI.lookup (heap, l))
    | Index (l,i) => Vector.sub (array (MapI.lookup (heap, l)), i)
    | Field (l,s) => MapS.lookup(cell_struct (MapI.lookup (heap,l)), s)

  fun put_stack ([], x, v) = raise CymbolError "Non-existant stack"
    | put_stack (map :: maps, x, v) = 
      case MapX.find (map, x) of 
        NONE => map :: put_stack (maps, x, v)
      | SOME _ => MapX.insert (map, x, v) :: maps

  fun put (S{heap, stack = T{stack, caller}}, addr, v) = 
    case addr of 
      Stack x => 
      S{heap = heap, 
        stack = T{stack = put_stack (stack, x, v), caller = caller}}
    | Heap l => 
      S{heap = MapI.insert (heap, l, Cell_val v),
        stack = T{stack = stack, caller = caller}}
    | Index (l,i) => 
      let val vs = array (MapI.lookup (heap,l)) in
      S{heap = MapI.insert (heap, l, Array (Vector.update(vs,i,v))),
        stack = T{stack = stack, caller = caller}} end
    | Field (l,s) => 
      let val vs = cell_struct (MapI.lookup (heap,l)) 
      in
        S{heap = MapI.insert (heap, l, Cell_struct (MapS.insert (vs, s, v))),
          stack = T{stack = stack, caller = caller}} 
      end

  fun declare (S{heap, stack = T{stack = stack, caller}}, x) =
      S{heap = heap,
        stack = T{stack = MapX.insert(hd stack, x, Uninitalized) :: tl stack,
                  caller = caller}}
       handle Empty => raise CymbolError "Local stack was empty"
    
  val new_state = 
      S{heap = MapI.empty, 
        stack = T{stack = [MapX.empty], caller = NONE}}

  fun new_cell (S{heap, stack}, l) = 
      S{heap = MapI.insert(heap, l, Cell(MapS.empty)),
        stack = stack}

  fun new_array (S{heap, stack}, l, size) = 
      S{heap = MapI.insert(heap, l, 
                           Array(Vector.tabulate(size, fn _ => Uninitalized))),
        stack = stack}
      

  fun init_fun (argn, argv) = 
      Vector.foldri
          (fn (i, name, stack) => 
              MapX.insert(stack, C0.Normal name, Vector.sub(argv,i)))
          MapX.empty
          argn

  fun push_fun (S{heap, stack = old_stack}, data, argn, argv) =
      S{heap = heap,
        stack = T{stack = [ init_fun (argn, argv) ],
                  caller = SOME (data, old_stack)}}
  fun pop_fun (S{heap, stack = T{caller, ...}}) = 
      case caller of
        NONE => NONE
      | SOME (data, stack) => SOME (S{heap = heap, stack = stack}, data)

  fun assign (state, x, v) = put (state, Stack x, v)
*)

(*
  (* Operations *)
  fun unop_action unop = 

*)

(*
    (*
    | C0.Monop(C0.Get, exp) =>
      let 
        val (state, v) = to_value (state, exp)
      in (state, Heap (pointer v)) end
    | C0.Binop(C0.Index, exp1, exp2) =>
      let 
        val (state, addr) = to_lvalue (state, exp1)
        val (state, v2) = to_value (state, exp2)
      in (state, offset_index (addr, Data.to_int (int v2))) end
    | C0.Binop(C0.Access, exp, C0.Field s) =>
      let 
        val (state, addr) = to_lvalue (state, exp)
      in (state, offset_field (addr, s)) end
    *)
    | _ => raise CymbolError "Unexpected lvalue"

  and to_value (state, exp) = 
    case exp of
    (*
      C0.IntConst i => (state, Int (Data.from_int i))
    | C0.BoolConst b => (state, Bool (Data.from_bool b))
    | C0.StringConst s => (state, String s)
    | C0.NULL => (state, Pointer 0)
    *)
      C0.Var x => (state, get (state, Stack x))
    | C0.Field s => raise CymbolError "Unexpected field"
    (*
    | C0.Monop(C0.Get,exp) => 
      let
        val (state, v) = to_value (state, exp)
      in (state, get (state, Heap (pointer v))) end 
    *)
    | C0.Monop(op1,exp) => 
      let
        val (state, v) = to_value (state, exp) 
      in (state, unop_action op1 v) end
    (*
    | C0.Binop(C0.Index,exp1,exp2) => 
      let 
        val (state, addr) = to_lvalue (state, exp1)
        val (state, v2) = to_value (state, exp2)
      in (state, get (state, offset_index(addr, Data.to_int (int v2)))) end
    | C0.Binop(C0.Access,exp,C0.Field s) => 
      let 
        val (state, addr) = to_lvalue (state, exp)
      in (state, get (state, offset_field(addr, s))) end
    | C0.Binop(C0.Access,_,_) => raise CymbolError "Expected a field here"
    | C0.Binop(C0.Put,exp1,exp2) => 
      let 
        val (state, addr) = to_lvalue (state, exp1)
        val (state, v2) = to_value (state, exp2)
      in (put (state, addr, v2), v2) end
    *)
    | C0.Binop(exp1,oper,exp2) => 
      let 
        val (state, v1) = to_value (state, exp1) 
        val (state, v2) = to_value (state, exp2)
      in (state, binop_action oper (v1,v2)) end
    (*
    | C0.Declare(x,NONE) => (declare(state,x), Nothing)
    | C0.Declare(x,SOME e) => 
      to_value (declare(state,x), C0.Binop(C0.Put, C0.Var x, e))
    *)
    | C0.AllocArray (typ, size) => 
      let 
        val l = gensym () 
        val (state, v) = to_value (state, size)
        val state = new_array (state, l, Data.to_int (int v))
      in (state, Pointer l) end
    | C0.Alloc typ => 
      let 
        val l = gensym () 
        val state = new_cell (state, l)
      in (state, Pointer l) end
    (*
    | C0.Func _ => 
      raise CymbolError "Functions should be lifted already"
    *)
    | C0.Ternary (exp, expT, expF) => 
      raise CymbolError "Ternary operations should be lifted already"

*)
end
