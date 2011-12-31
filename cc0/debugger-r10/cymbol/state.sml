(* Unified state for Cymbol *)
(* Robert J. Simmons            *)

signature VALUES = sig

  type value
  type boolrep
  type intrep
  type addr
  
  val int         : intrep  -> value
  val bool        : boolrep -> value
  val char        : char    -> value
  val string      : string  -> value
  val null        : value
  val unit        : value
  val to_int      : value   -> intrep
  val to_bool     : value   -> boolrep
  val to_string   : value   -> string
  val to_function : value   -> string
  val to_addr     : value   -> addr

  val value_eq      : value * value -> boolrep
  val value_neq     : value * value -> boolrep

  val stringify : value   -> string

end

signature STATE = sig

  type 'a state   (* The state object    *)

  include VALUES

  (* Generating states *)
  val new_state : 
      {ty_vars : C0.ty MapS.map,
       struct_defs : (C0.ty * string) list MapS.map,
       initial_function : string} -> 'a state
  val current_function : 'a state -> string

  (* The "heap" is everything that isn't the call stack *)
  type 'a heap 
  val get_heap : 'a state -> 'a heap
  val put_heap : 'a state * 'a heap -> 'a state

  (* Functions are tricky - this is a way to backpatch function evaluation *)
  type 'a magicfun 
    = ('a state * string * value list) -> ('a state * value option)
  val get_magicfun : 'a state -> 'a magicfun
  val put_magicfun : 'a state * 'a magicfun -> 'a state

  (* Scoping *)
  val push_fun     : 'a state * string * 'a -> 'a state
  val pop_fun      : 'a state -> ('a state * string * 'a) option
  val push_scope   : 'a state -> 'a state
  val pop_scope    : 'a state -> 'a state

  (* Stack allocated storage *)
  val declare      : 'a state * C0.ty * C0.ident -> 'a state
  val get_id       : 'a state * C0.ident -> value
  val put_id       : 'a state * C0.ident * value -> 'a state

  (* Heap allocated storage *)
  val alloc        : 'a state * C0.ty -> 'a state * value
  val alloc_array  : 'a state * C0.ty * intrep -> 'a state * value
  val get_addr     : 'a state * addr -> value
  val put_addr     : 'a state * addr * value -> 'a state

  (* Address offsets *)
  val offset_index : addr * intrep -> addr
  val offset_field : addr * string -> addr

  (* Debugging *)
  val print_state  : 'a state -> unit

end

functor State (Data : DATA) 
        :> STATE where type boolrep = Data.boolrep 
                 and type intrep = Data.intrep 
= struct

  (* Data types *)
 
  type boolrep = Data.boolrep
  type intrep = Data.intrep

  datatype addr 
    = Heap  of int
    | Index of int * int 
    | Field of addr * string

  val offset_index = fn (Heap l, i) => Index (l, Data.to_int i)
                      | (_,_) => raise Error.Internal "invalid array offset"
  val offset_field = Field

  datatype value 
    = Unit
    | Int of intrep 
    | Bool of boolrep
    | Char of char
    | String of string
    | NullPointer
    | EmptyArray
    | PseudoStruct of string
    | Array of C0.ty * int * int
    | Function of string
    | Pointer of C0.ty * int
    | Uninitialized

  datatype 'a stack
    = T of {f : string,
            stack  : value MapX.map list, 
            caller : ('a * 'a stack) option}
      
  datatype mem
    = Struct of (string * mem MapS.map)
    | Value of value

  datatype mem' 
    = One of mem | Some of C0.ty * mem vector

  datatype 'a state
    = S of {types  : C0.ty MapS.map * (C0.ty * string) list MapS.map, 
            heap   : mem' MapI.map * int,
            stack  : 'a stack,
            magicfun : 
            ('a state * string * value list) -> ('a state * value option)}

  type 'a magicfun 
    = ('a state * string * value list) -> ('a state * value option)

  exception ArrayOutOfBounds


  (* Printing the state *)

  fun stringify v = 
    case v of
      Unit           => ("(void)")
    | Int i          => (Data.int_to_string i ^ " (int)")
    | Bool b         => (Data.bool_to_string b ^ " (bool)")
    | Char c         => ("'" ^ String.str c ^ "' (char)")
    | String s       => ("\"" ^ s ^ "\" (string)") 
    | Function f     => ("(code pointer to function " ^ f ^ ")")
    | PseudoStruct s => ("(struct " ^ s ^ ")")
    | NullPointer    => ("(null pointer)")
    | Pointer(ty,l)  => ("loc0x" ^ Word.toString (Word.fromInt l) ^ 
                        " (" ^ C0.ty_string ty ^ " pointer)")
    | EmptyArray     => ("(empty array)")
    | Array(ty,l,n)  => ("loc0x" ^ Word.toString (Word.fromInt l) ^
                        " (" ^ Int.toString n ^ "-element " ^
                        C0.ty_string ty ^ " array)")
    | Uninitialized  => ("(uninitialized stack location)")

  fun print_stack stack =
    let in 
      app (fn (C0.Normal x, v) => print (x ^ " --> " ^ stringify v ^ "\n")
            | (_, v) => print ("TEMP --> " ^ stringify v ^ "\n"))
          (MapX.listItemsi stack)
    end

  fun print_mem (i,mem) = ()
  (*
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
  *)

  fun print_state (S{heap, stack = T{f, stack, caller}, ...}) = 
    let in
      print "----- Stack: -----\n";
      app print_stack stack (*;
      print "----- Heap: ------\n";
      MapI.appi print_mem heap *)
    end    

  (* Projecting into and out of the value type *)

  val val_desc = 
    fn Unit => "void"
     | Int _ => "int"
     | Bool _ => "bool"
     | Char _ => "char"
     | String _ => "string"
     | NullPointer => "null pointer"
     | Pointer (ty, _) => C0.ty_string ty ^ " *"
     | EmptyArray => "empty array"
     | PseudoStruct s => "struct " ^ s
     | Array (ty, _, _) => C0.ty_string ty ^ " []"
     | Function _ => "function"
     | Uninitalized => "uninitialized value"

  val int = Int
  val bool = Bool
  val char = Char
  val string = String
  val unit = Unit
  val null = NullPointer
  val to_int = fn Int i => i 
   | v => raise Error.Dynamic ("cannot cast " ^ val_desc v ^ " to int")
  val to_bool = fn Bool b => b
   | v => raise Error.Dynamic ("cannot cast " ^ val_desc v ^ " to bool")
  val to_string = fn String s => s 
   | v => raise Error.Dynamic ("cannot cast " ^ val_desc v ^ " to string")
  val to_function = fn Function f => f 
   | v => raise Error.Dynamic ("cannot cast " ^ val_desc v ^ " to function")
  val to_addr = fn Array (_,l,_) => Heap l | Pointer (_,l) => Heap l
   | v => raise Error.Dynamic ("cannot cast " ^ val_desc v ^ " to function")

  fun value_eq vs = 
    case vs of 
      (Unit, Unit) => Data.from_bool true
    | (Int i1, Int i2) => Data.int_eq (i1, i2)
    | (Bool b1, Bool b2) => Data.bool_eq (b1, b2)
    | (Char c1, Char c2) => Data.from_bool (c1 = c2)
    | (String s1, String s2) => Data.from_bool (s1 = s2)
    | (NullPointer, NullPointer) => Data.from_bool true
    | (Function f1, Function f2) => Data.from_bool (f1 = f2)
    | (Pointer p1, Pointer p2) => Data.from_bool (p1 = p2)
    | (EmptyArray, EmptyArray) => Data.from_bool true
    | (Array (_, l1, _), Array (_, l2, _)) => Data.from_bool (l1 = l2)
    | (v1,v2) => 
      raise Error.Dynamic 
                ("cannot compare a " ^ val_desc v1 ^ " and a " ^ val_desc v2)
  
  val value_neq = Data.bool_not o value_eq

  (* Generating states *)

  val mem_zero = 1024 * 1024

  val new_state = fn {ty_vars, struct_defs, initial_function} =>
      S{types = (ty_vars, struct_defs),
        heap = (MapI.empty, mem_zero), 
        stack = T{f = initial_function, stack = [MapX.empty], caller = NONE},
        magicfun = fn _ => raise Error.Internal "no magic function"}

  val current_function = fn S{stack = T{f, ...}, ...} => f

  type 'a heap = (mem' MapI.map * int) * 'a magicfun 

  fun get_heap (S{heap, magicfun, ...} : 'a state) : 'a heap = 
      (heap, fn x => magicfun x)

  fun put_heap (S{types, stack, ...}, 
                ((heap, magicfun) : 'a heap)) =
      S{types = types, heap = heap, stack = stack, magicfun = magicfun}

  (* Dealing with the magic functions *)

  fun put_magicfun (S{types, heap, stack, magicfun}, f) = 
      S{types = types,
        heap = heap, 
        stack = stack,
        magicfun = f}
  
  fun get_magicfun (S{magicfun, ...}) = magicfun

  (* Scoping of functions and blocks *)

  fun push_fun (S{types,
                  heap, 
                  stack = old_stack, 
                  magicfun}, f, data) =
      S{types = types,
        heap = heap,
        stack = T{f = f, stack = [ MapX.empty ],
                  caller = SOME (data, old_stack)},
       magicfun = magicfun}

  fun pop_fun (S{types,
                 heap, 
                 stack = T{caller, ...},
                 magicfun}) = 
      case caller of
        NONE => NONE
      | SOME (data, stack as T{f,...}) => 
        SOME (S{types = types,
                heap = heap, 
                stack = stack,
                magicfun = magicfun}, f, data)

  fun push_scope (S{types,
                    heap,
                    stack = T{f, stack, caller},
                    magicfun}) =
      let in
        S{types = types,
          heap = heap,
          stack = T{f = f, stack = MapX.empty :: stack, caller = caller},
          magicfun = magicfun}
      end

  fun pop_scope (S{types,
                   heap,
                   stack = T{f, stack, caller},
                   magicfun}) =
      let in
        S{types = types,
          heap = heap,
          stack = T{f = f, stack = tl stack, caller = caller},
          magicfun = magicfun}
        handle Empty => raise Error.Internal "no more scopes to pop out of"
      end

  (* Default values and memory locations *)

  fun find_ty ty_defs =
    C0.find_ty (fn s => case MapS.find (ty_defs, s) of
         NONE => raise Error.Dynamic ("no definition for type variable " ^ s)
       | SOME ty => ty) 

  fun default_value ty = 
    case ty of
      C0.TyUnit => Unit
    | C0.TyChar => Char #"\^@"
    | C0.TyString => String ""
    | C0.TyVar s => raise Error.Internal ("no available default value for " ^ s)
    | C0.TyInt => Int (Data.from_int 0wx0)
    | C0.TyBool => Bool (Data.from_bool false)
    | C0.TyPointer _ => NullPointer
    | C0.TyArray _ => EmptyArray
    | C0.TyStruct _ => raise Error.Internal ("no default value for structs")

  fun default_mem struct_defs ty =
    case ty of
      C0.TyStruct s => 
      let val fields = case MapS.find (struct_defs, s) of
              NONE => raise Error.Dynamic ("struct " ^ s ^ " not defined")
            | SOME fields => fields
        fun folder ((ty, s), map) = 
            MapS.insert(map, s, default_mem struct_defs ty)
        val mem = List.foldr folder MapS.empty fields
      in Struct (s, mem) end
    | ty => Value (default_value ty)

  (* Stack allocated storage *)

  fun declare (S{stack = T{stack = [], ...}, ...}, ty, x) = 
      raise Error.Internal "cannot declare a variable with no stack"
    | declare (S{types,
                 heap, 
                 stack = T{f, stack = top :: stack, caller},
                 magicfun}, ty, x) =
      S{types = types,
        heap = heap,
        stack = T{f = f,
                  stack = MapX.insert(top, x, Uninitialized) :: stack,
                  caller = caller},
        magicfun = magicfun}

  fun get_stack ([], C0.Temp _) = 
      raise Error.Dynamic "undefined temporary variable"
    | get_stack ([], C0.Normal f) = Function f (* XXX fix this *)
    | get_stack (map :: maps, x) = 
      case MapX.find (map, x) of
        NONE => get_stack (maps, x)
      | SOME v => v

  fun get_id (S{stack = T{stack, ...}, ...}, x) = get_stack (stack, x)

  fun put_stack ([], C0.Normal x, v) =
      raise Error.Dynamic ("undeclared variable " ^ x)
    | put_stack ([], C0.Temp _, v) =
      raise Error.Internal ("undeclared temporary variable")
    | put_stack (map :: maps, x, v) = 
      case MapX.find (map, x) of 
        NONE => map :: put_stack (maps, x, v)
      | SOME _ => MapX.insert (map, x, v) :: maps

  fun put_id (S{types,
                heap, 
                stack = T{f, stack, caller},
                magicfun}, x, v) =
      S{types = types,
        heap = heap,
        stack = T{f = f,
                  stack = put_stack (stack, x, v),
                  caller = caller},
        magicfun = magicfun} 

  (* Heap allocated storage *)
 
  fun alloc (S{types = (ty_vars, struct_defs),
               heap = (heap, max), 
               stack,
               magicfun}, ty) =
      (S{types = (ty_vars, struct_defs),
         heap = (MapI.insert(heap, max,
                         One (default_mem struct_defs (find_ty ty_vars ty))), 
                 max + 1),
         stack = stack,
         magicfun = magicfun}, Pointer(find_ty ty_vars ty, max))

  fun alloc_array (S{types = (ty_vars, struct_defs),
                     heap = (heap, max), 
                     stack,
                     magicfun}, ty, i) =
      let
        val i = Data.to_int i
        val newmem = default_mem struct_defs (find_ty ty_vars ty)
        val newmem' = Some (ty, Vector.tabulate (i, (fn _ => newmem)))
      in
        (S{types = (ty_vars, struct_defs),
           heap = (MapI.insert(heap, max, newmem'), max + 1),
           stack = stack,
           magicfun = magicfun},
         Array(find_ty ty_vars ty, max, i))
      end

  fun safe_sub (mems, i) = 
      Vector.sub(mems, i)
      handle Subscript => 
             raise Error.ArrayOutOfBounds(i, Vector.length mems)

  fun get_from_mem (heap, addr) = 
    case addr of
      Heap l => 
      (case MapI.lookup(heap, l) of
         One mem => mem
       | Some (ty, mems) => Value (Array (ty, l, Vector.length mems)))
    | Index(l,i) => 
      (case MapI.lookup(heap, l) of
         One mem => 
         raise Error.Dynamic "can't treat a pointer as an array"
       | Some (ty, mems) => safe_sub (mems, i))
    | Field(addr, f) =>
      (case get_from_mem (heap, addr) of
         Value v => 
         raise Error.Dynamic ("can't get field " ^f ^ " from a " ^ val_desc v)
       | Struct (s, map) => 
         (case MapS.find (map, f) of 
            NONE =>
            raise Error.Dynamic ("struct " ^ s ^ " does not have a field " ^ f)
          | SOME mem => mem))

  fun get_addr (S{heap = (heap,_), ...}, addr) =
    case get_from_mem (heap, addr) of
      Value v => v
    | Struct (s, _) => PseudoStruct s

  fun modify_mem (mem, v, offsets) =
    case (mem, offsets) of
      (Value _, []) => Value v
    | (Struct (s,mems), f :: offsets) =>
      let val mem = 
              case MapS.find (mems, f) of
                NONE => 
                raise Error.Dynamic ("struct "^s^" does not have a field "^f)
              | SOME mem => modify_mem (mem, v, offsets)
      in Struct (s, MapS.insert(mems, f, mem)) end
    | (Struct (s,_), []) => 
      raise Error.Dynamic ("updating a struct directly is not permitted")
    | (Value v, f :: _) =>
      raise Error.Dynamic
                ("tried to update field " ^ f ^ "of a " ^ val_desc v)

  fun modify_heap (heap, addr, v, offsets) = 
    case addr of 
      Heap l =>
      let val mem = 
              case MapI.lookup(heap, l) of 
                One mem => mem
              | Some _ => 
                raise Error.Dynamic "can't treat an array as a pointer"
        val new_mem = modify_mem (mem, v, offsets)
        val new_mem' = One new_mem
      in MapI.insert(heap, l, new_mem') end
    | Index (l, i) =>
      let val (ty, mems) = 
              case MapI.lookup(heap, l) of
                One mem => 
                raise Error.Dynamic "can't treat a pointer as an array"
              | Some (ty, mems) => (ty, mems)
        val new_mem = modify_mem (safe_sub (mems, i), v, offsets)
        val new_mem' = Some (ty, Vector.update (mems, i, new_mem))
      in MapI.insert(heap, l, new_mem') end
    | Field (addr, s) => modify_heap (heap, addr, v, s :: offsets)
                                   

  fun put_addr (S{types,
                  heap = (heap, max), 
                  stack,
                  magicfun}, addr, v) =
      (S{types = types,
        heap = (modify_heap (heap, addr, v, []), max),
        stack = stack,
        magicfun = magicfun})


(*

  local val v = ref 0 in
  fun gensym() = (v := !v + 1; !v)
  end

  type boolrep = Data.boolrep
  type intrep = Data.intrep
  exception TypeCast
  exception Unimp
  exception CymbolError of string

  datatype value 
    = Int of intrep 
    | Bool of boolrep
    | String of string
    | Pointer of int (* Pointer to zero is the null pointer *)
    | Uninitalized
    | Nothing


  val int = fn Int i => i | _ => raise TypeCast
  val bool = fn Bool b => b | _ => raise TypeCast
  val string = fn String s => s | _ => raise TypeCast
  val pointer = fn Pointer x => x | _ => raise TypeCast
  val Cell_val    = fn v => Cell (MapS.singleton ("",v))
  val Cell_struct = fn vs => Cell vs
  val cell_val = fn Cell (vs) => (case MapS.find (vs, "") of
                                    NONE => Uninitalized
                                  | SOME v => v)
                  | _ => raise TypeCast
  val cell_struct = fn Cell vs => vs | _ => raise TypeCast
  val array = fn Array a => a | _ => raise TypeCast   




    

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

    
  fun new_cell (S{heap, stack}, l) = 
      S{heap = MapI.insert(heap, l, Cell(MapS.empty)),
        stack = stack}

  fun new_array (S{heap, stack}, l, size) = 
      S{heap = MapI.insert(heap, l, 
                           Array(Vector.tabulate(size, fn _ => Uninitalized))),
        stack = stack}
      


  fun assign (state, x, v) = put (state, Stack x, v)

  (* Operations *)
  fun unop_action unop = 
    case unop of
      C0.LogicNot => Bool o Data.bool_not o bool
    | C0.ArithNeg => Int o Data.int_not o int
    | C0.BitNot   => Int o Data.bit_not o int

  fun zip (f,g) (x,y) = (f x, g y)

  fun binop_action binop = 
    case binop of
      C0.Plus       => Int  o Data.int_add    o zip(int,int)
    | C0.Times      => Int  o Data.int_mul    o zip(int,int)
    | C0.Minus      => Int  o Data.int_sub    o zip(int,int)
    | C0.Mod        => Int  o Data.int_mod    o zip(int,int)
    | C0.Div        => Int  o Data.int_div    o zip(int,int)
    (* XXX INCORRECT these three should be short circuting *)
    | C0.LogicAnd   => Bool o Data.bool_and   o zip(bool,bool)
    | C0.LogicOr    => Bool o Data.bool_or    o zip(bool,bool)
    | C0.LogicImp   => Bool o Data.bool_imp   o zip(bool,bool)
    | C0.BitAnd     => Int  o Data.int_bitand o zip(int,int)
    | C0.BitOr      => Int  o Data.int_bitor  o zip(int,int)
    | C0.BitXor     => Int  o Data.int_bitxor o zip(int,int)
    | C0.Lt         => Bool o Data.int_lt     o zip(int,int)
    | C0.Leq        => Bool o Data.int_leq    o zip(int,int)
    | C0.Eq         => Bool o Data.int_eq     o zip(int,int)
    | C0.Geq        => Bool o Data.int_geq    o zip(int,int)
    | C0.Gt         => Bool o Data.int_gt     o zip(int,int)
    | C0.Neq        => Bool o Data.int_neq    o zip(int,int)
    | C0.ShiftLeft  => raise Unimp
    | C0.ShiftRight => raise Unimp

  (* Evaluation to value *)
  fun to_lvalue (state, lval) = 
    case lval of 
      C0.LHSVar x => (state, Stack x)
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
