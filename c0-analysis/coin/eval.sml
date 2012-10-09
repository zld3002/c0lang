(* Implement the operational semantics of C0 expressions *)

(* If Coin is modified so that the Call expression is eliminated 
 * in favor of a Call command, then the second argument to eval_exp and
 * eval_lval could be eliminated; these are only passed around to handle
 * possible function applications. - rjs 14 Feb 2012 *)

(* The state is mostly passed around for its utility functions, but it is also
 * necessary to update the state at times because the alloc() and alloc_array()
 * primitive expressions are side-effecting. I don't know if the compiler code 
 * that hoists functions also hoists alloc and alloc_array, but we should 
 * answer that. - rjs 14 Feb 2012 *)

structure Eval:> sig

  datatype loc = 
     NullLoc 
   | StackLoc of Symbol.symbol
   | HeapLoc of Ast.tp * ConcreteState.addr

  val get: 'a ConcreteState.state * loc -> ConcreteState.value
  val put: 'a ConcreteState.state * loc * ConcreteState.value -> unit

  val eval_exp: 
     'a ConcreteState.state
     -> C0Internal.exp 
     -> ConcreteState.value

  val eval_lval:
     'a ConcreteState.state
     -> C0Internal.exp
     -> loc

  val eval_monop:
     C0Internal.monop
     -> ConcreteState.value
     -> ConcreteState.value

  val eval_binop:
     C0Internal.binop
     -> ConcreteState.value * ConcreteState.value
     -> ConcreteState.value

end = 
struct

  structure D = ConcreteData
  structure S = ConcreteState
  structure C0 = C0Internal

  type 'a state = 'a S.state
  type addr = S.addr
  type value = S.value 

  datatype loc = NullLoc | StackLoc of Symbol.symbol | HeapLoc of Ast.tp * addr

  fun get (state, NullLoc) = raise Error.NullPointer
    | get (state, StackLoc x) = S.get_id (state, x)
    | get (state, HeapLoc (ty, addr)) = S.get_addr (state, (ty, addr))

  fun put (state, NullLoc, v) = raise Error.NullPointer
    | put (state, StackLoc x, v) = S.put_id (state, x, v)
    | put (state, HeapLoc (ty, addr), v) = 
        (S.put_addr (state, (ty, addr), v)
          handle (Error.NullPointer) => 
            TextIO.output(TextIO.stdErr,"Allocated to a NULL addr\n"))
  
  fun eval_const c = 
    case c of  
      C0.Bool b => S.bool (D.from_bool b)
    | C0.Int i => S.int (D.from_int i)
    | C0.Char c => S.char c
    | C0.String s => S.string s
    | C0.NullPointer => S.null

  fun zip (f,g) (x,y) = (f x, g y)

  fun eval_monop monop = 
    case monop of 
      C0.LogicNot => S.bool o D.bool_not o S.to_bool
    | C0.ArithNeg => S.int o D.int_not o S.to_int
    | C0.BitNot   => S.int o D.bit_not o S.to_int
     
  fun eval_binop binop = 
    case binop of
      C0.Plus       => S.int  o D.int_add    o zip(S.to_int,S.to_int)
    | C0.Times      => S.int  o D.int_mul    o zip(S.to_int,S.to_int)
    | C0.Minus      => S.int  o D.int_sub    o zip(S.to_int,S.to_int)
    | C0.Div        => S.int  o D.int_div    o zip(S.to_int,S.to_int)
    | C0.Mod        => S.int  o D.int_mod    o zip(S.to_int,S.to_int)
    | C0.BitAnd     => S.int  o D.int_bitand o zip(S.to_int,S.to_int)
    | C0.BitOr      => S.int  o D.int_bitor  o zip(S.to_int,S.to_int)
    | C0.BitXor     => S.int  o D.int_bitxor o zip(S.to_int,S.to_int)
    | C0.ShiftLeft  => S.int  o D.int_shiftl o zip(S.to_int,S.to_int)
    | C0.ShiftRight => S.int  o D.int_shiftr o zip(S.to_int,S.to_int)
    | C0.Neq        => S.bool o D.bool_not   o S.value_eq
    | C0.Lt         => S.bool o (fn (x, y) => S.value_lt (x, y))
    | C0.Gt         => S.bool o (fn (x, y) => S.value_lt (y, x))
    | C0.Eq         => S.bool o S.value_eq
    | C0.Leq => 
      (fn (x, y) => S.bool (D.bool_or (S.value_eq (x, y), S.value_lt (x, y))))
    | C0.Geq => 
      (fn (x, y) => S.bool (D.bool_or (S.value_eq (y, x), S.value_lt (y, x))))
    | C0.Addr => raise Error.Internal ("Unexpected binary operator: address of") 

  fun to_heap loc = 
    case loc of
      NullLoc => raise Error.NullPointer
    | StackLoc _ => 
      raise Error.Dynamic "stack location given; heap location is required"
    | HeapLoc (ty, addr) => (ty, addr)

  fun to_struct ty = 
    case ty of
      Ast.StructName st => st
    | ty => raise Error.Dynamic ("expected struct, got " ^ Ast.Print.pp_tp ty)

  fun eval_lval state exp = 
    let 
       val ev_exp = eval_exp state 
       val ev_lval = eval_lval state
    in
       case exp of 
         C0.Var x => StackLoc x
       | C0.Ref exp => 
         (case S.to_pointer (ev_exp exp) of
             NONE => NullLoc
           | SOME (ty, addr) => HeapLoc (ty, addr))
       | C0.Field (exp, field) => 
         let 
            val (ty, addr) = to_heap (ev_lval exp)
         in HeapLoc (S.offset_field (state, addr, to_struct ty, field)) end
       | C0.Index (exp, expi) =>
         let  
            val (ty, addr, n) = S.to_array (ev_exp exp)
            val i = D.to_int (S.to_int (ev_exp expi))
         in 
            if i >= 0 andalso i < n 
            then HeapLoc (ty, S.offset_index (state, addr, i))
            else raise Error.ArrayOutOfBounds (i, n)
         end
       | C0.Ternary (exp, expT, expF) => 
         let val v = ev_exp exp in
            if D.to_bool (S.to_bool v)
            then ev_lval expT else ev_lval expF
         end
       | _ => raise Error.Dynamic "invalid lvalue"
    end

  and eval_exps state exps = 
    map (eval_exp state) exps
  and eval_exp state exp = 
    let 
       val ev_exp = eval_exp state 
       val ev_lval = eval_lval state
    in
       case exp of
       (* Constants and variables *)
         C0.Const c => eval_const c
       | C0.Var x => S.get_id (state, x)

       (* Primitive operations, including short-circuting logic operations *)
       | C0.LogicOr (exp1, exp2) =>
         if D.to_bool (S.to_bool (ev_exp exp1)) 
         then S.bool true else ev_exp exp2
       | C0.LogicAnd (exp1, exp2) =>
         if D.to_bool (S.to_bool (ev_exp exp1)) 
         then ev_exp exp2 else S.bool false
       | C0.Binop (exp1, oper, exp2) =>
         eval_binop oper (ev_exp exp1, ev_exp exp2)
       | C0.Monop (oper, exp) =>
         eval_monop oper (ev_exp exp)
       | C0.Ternary (exp, expT, expF) =>
         if D.to_bool (S.to_bool (ev_exp exp))
         then ev_exp expT else ev_exp expF
       | C0.Length exp => 
         let val (ty, addr, n) = S.to_array (ev_exp exp)
         in S.int (D.from_int (Word32.fromInt n)) end 

       (* State allocation *)
       | C0.Alloc ty => S.alloc (state, ty)
       | C0.AllocArray (ty, exp) => 
         let val i = S.to_int (ev_exp exp) in
            if D.to_int i < 0 
            then raise Error.ArraySizeNegative (D.to_int i) 
            else S.alloc_array (state, ty, i)
         end

       (* State access *)
       | C0.Ref exp =>
         (case S.to_pointer (ev_exp exp) of
             NONE => raise Error.NullPointer
           | SOME (ty, addr) => S.get_addr (state, (ty, addr)))
       | C0.Field (exp, field) => 
         let 
            val (ty, addr) = to_heap (ev_lval exp)
            val addr = S.offset_field (state, addr, to_struct ty, field)
         in S.get_addr (state, addr) end
       | C0.Index (exp, expi) =>
         let
           val (ty, addr, n) = S.to_array (ev_exp exp)
           val i = D.to_int (S.to_int (ev_exp expi))
         in
           if i >= 0 andalso i < n 
           then S.get_addr (state, (ty, S.offset_index (state, addr, i)))
           else raise Error.ArrayOutOfBounds (i, n)
         end
       | C0.Call _ => 
          raise Error.Internal "Unexpected call expression; should be CCall stm after hoisting"
    end

end
