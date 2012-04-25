(* Unified state for Cymbol *)
(* Relies on compiler (Ast) types and Symbol.symbol identifiers *)
(* Robert J. Simmons *)

functor StateFn (structure Data : DATA
                 structure Heap : HEAP
                    where type bool_rep = Data.bool_rep
                      and type int_rep = Data.int_rep 
                      and type char_rep = char) 
        :> STATE where type bool_rep = Data.bool_rep 
                   and type int_rep = Data.int_rep
                   and type native_pointer = Heap.native_pointer
= struct

  (* == DATA TYPES == *)
 
  type bool_rep = Data.bool_rep
  type int_rep = Data.int_rep
  type string_rep = Heap.string_rep
  type native_pointer = Heap.native_pointer

  datatype value 
    = Unit
    | Int of int_rep 
    | Bool of bool_rep
    | Char of char
    | String of string_rep
    | NullPointer
    | PseudoStruct of Symbol.symbol * string
    | Array of Ast.tp * Heap.loc * int
    | Function of string * Ast.tp * Ast.tp list 
    | Pointer of Ast.tp * Heap.loc
    | Uninitialized

  type heap = Heap.heap
  datatype 'a stack
    = T of {fun_name : Symbol.symbol,
            locals   : (Ast.tp Symbol.table * value Symbol.table) list, 
            caller   : ('a * 'a stack) option,
            depth    : int}

  datatype 'a state
    = S of {typedefs     : Ast.tp -> Ast.tp, 
            structdefs   : Symbol.symbol -> (Ast.tp * Symbol.symbol) list,
            functions    : Symbol.symbol -> (Ast.tp * Ast.tp list) option,
            heap         : heap,
            magic        : Symbol.symbol * value list * 'a state -> value,
            stack        : 'a stack ref}

  (* == CHECKPOINTING == *)
          
  type 'a checkpoint = 'a stack * Heap.checkpoint
  fun checkpoint (S{stack = ref stack, heap, ...}) = 
      (stack, Heap.checkpoint heap)
  fun restore (S{stack, heap, ...}, (old_stack, old_heap)) = 
      (stack := old_stack; Heap.restore (heap, old_heap))


  (* == PRINTING == *)

  (* Handle the delta between c0 chars and C chars *)
  fun printableChar c = 
     c = #"\000" 
     orelse (c >= #"\a" andalso c <= #"\r")
     orelse (c >= #" " andalso c <= #"~")

  fun toCChar #"\000" = "\\0"
    | toCChar c = Char.toCString c

  fun toCString s = String.translate toCChar s

  fun addr_string (loc,_,_) = Heap.loc_string loc

  fun value_string v = 
    case v of
      Unit            => ("(void)")
    | Int i           => (Data.int_to_string i ^ " (int)")
    | Bool b          => (Data.bool_to_string b ^ " (bool)")
    | Char c          => 
      if printableChar c 
      then ("'" ^ toCChar c ^ "' (char)")
      else ("(non-displayable char with ordinal value " 
            ^ Int.toString (ord c) ^ ")")
    | String s        => 
      let val split = String.fields (not o printableChar) (Heap.rep_to_str s) in
         if length split = 1
         then ("\"" ^ toCString (hd split) ^ "\" (string)") 
         else ("(string with non-displayable char at position " ^ 
               Int.toString (size (hd split)) ^ ")")
      end
    | Function(f,t,a) => ("(code pointer to function " 
                          ^ Ast.Print.pp_tp t ^ " " ^ f ^ "(" ^
                          String.concatWith "," (map Ast.Print.pp_tp a) ^  "))")
    | PseudoStruct (s, addr)  => (addr ^ " (struct " ^ Symbol.name s ^ ")")
    | NullPointer     => ("NULL (pointer of unknown type)")
    | Pointer(ty,loc) => (Heap.loc_string loc ^
                          " (" ^ Ast.Print.pp_tp ty ^ "*)")
    | Array(ty,loc,n) => (Heap.loc_string loc ^
                          " (" ^ Ast.Print.pp_tp (Ast.Array ty) ^ 
                          " with " ^ Int.toString n ^ 
                          (if n = 1 then " element)" else " elements)"))
    | Uninitialized   => ("(uninitialized value)")
 
  fun value_desc v = 
    case v of
      Unit => "void"
    | Int _ => "int"
    | Bool _ => "bool"
    | Char _ => "char"
    | String _ => "string"
    | NullPointer => "null pointer"
    | Pointer (ty, _) => Ast.Print.pp_tp ty ^ "*"
    | PseudoStruct (s, _) => "struct " ^ Symbol.name s
    | Array (ty, _, _) => Ast.Print.pp_tp ty ^ "[]"
    | Function _ => "function"
    | Uninitalized => "uninitialized value"



  (* == VALUE TYPE == *)
 
  fun ty_eq t1 t2 =
     case (t1, t2) of  
        (Ast.Int, Ast.Int) => true
      | (Ast.Bool, Ast.Bool) => true
      | (Ast.String, Ast.String) => true
      | (Ast.Char, Ast.Char) => true
      | (Ast.Pointer t1, Ast.Pointer t2) => ty_eq t1 t2
      | (Ast.Array t1, Ast.Array t2) => ty_eq t1 t2
      | (Ast.StructName x, Ast.StructName y) => EQUAL = Symbol.compare (x, y)
      | (Ast.Void, Ast.Void) => true
      | _ => false

  (* We only have to typecheck assignable values! 

      igillis 4/22/12: This is no longer true with the new addrof operator
      added to go along with fp's hoisting mechanism. *)
  fun typecheck (v, ty) = ty_eq ty Ast.Any orelse
    case v of 
      Unit => ty_eq ty Ast.Void
    | Int _ => ty_eq ty Ast.Int
    | Bool _ => ty_eq ty Ast.Bool
    | Char _ => ty_eq ty Ast.Char
    | String _ => ty_eq ty Ast.String
    | NullPointer => (case ty of Ast.Pointer _ => true | _ => false)
    | Pointer (ty', _) => 
      (case ty of Ast.Pointer ty => ty_eq ty ty' | _ => false)
    | Array (ty', _, _) => 
      (case ty of Ast.Array ty => ty_eq ty ty' | _ => false)
    | Function _ => false
    | Uninitialized => false
    | PseudoStruct _ => false

  fun assert (v, ty) = 
      if typecheck (v, ty) then ()
      else raise Error.Dynamic ("assigning " ^ value_desc v ^
                                " where a value of type " ^ Ast.Print.pp_tp ty
                                ^ " is expected")

  fun novars ty = 
     case ty of
        Ast.Pointer ty => novars ty
      | Ast.Array ty => novars ty
      | Ast.TypeName name => 
        raise Error.Internal ("Type name " ^ Symbol.name name ^ " included")
      | _ => ()

        

  val to_native =
   fn (loc, NONE, []) => Heap.to_native loc
    | _ => raise Error.Internal "pointers with offsets (pointer arithmetic)"
  val from_native = fn ptr => (Heap.from_native ptr, NONE, [])

  val int = Int
  val bool = Bool
  val char = Char
  val string = String o Heap.str_to_rep
  val pointer = 
   fn (ty, (loc, NONE, [])) => (novars ty; Pointer (ty, loc))
    | (ty, (loc, ind, offs)) => (novars ty; Pointer(ty, Heap.addr_sub' (loc,ind,offs)))
    (*| _ => raise Error.Internal "pointers with offsets (pointer arithmetic)"*)
  val array = 
   fn (ty, (loc, NONE, []), n) => (novars ty; Array (ty, loc, n))
    | _ => raise Error.Internal "array with offsets (pointer arithmetic)"
  val unit = Unit
  val null = NullPointer
  val to_int = fn Int i => i 
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to int")
  val to_bool = fn Bool b => b
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to bool")
  val to_char = fn Char c => c
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to char")
  val to_string = fn String s => (Heap.rep_to_str s) 
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to string")
  val to_function = fn Function (f, _, _) => f 
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to function")
  val to_pointer = 
   fn Pointer (ty, loc) => 
      if Heap.null loc then NONE else SOME (ty, (loc, NONE, []))
    | NullPointer => NONE
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to pointer")
  val to_array = fn Array (ty, loc, i) => (ty, (loc, NONE, []), i)
    | Uninitialized => raise Error.Uninitialized
    | v => raise Error.Dynamic ("cannot cast " ^ value_desc v ^ " to array")

  (* == GENERIC EQUALITY == *)

  fun value_lt vs =
    case vs of 
      (Int i1, Int i2) => Data.int_lt (i1, i2)
    | (Char c1, Char c2) => Data.from_bool (ord c1 < ord c2)
    | (v1,v2) => 
      raise Error.Dynamic 
            ("cannot compare a " ^ value_desc v1 ^ " and a " ^ value_desc v2
             ^ " for inequality")

  fun value_eq vs = 
    case vs of 
      (Unit, Unit) => Data.from_bool true
    | (Int i1, Int i2) => Data.int_eq (i1, i2)
    | (Bool b1, Bool b2) => Data.bool_eq (b1, b2)
    | (Char c1, Char c2) => Data.from_bool (c1 = c2)
    | (NullPointer, NullPointer) => Data.from_bool true
    | (NullPointer, Pointer (_, loc)) => Data.from_bool (Heap.null loc)
    | (Pointer (_, loc), NullPointer) => Data.from_bool (Heap.null loc)
    | (Pointer (_, l1), Pointer (_, l2)) => Data.from_bool (Heap.eq (l1, l2))
    | (Function (f1, _, _), Function (f2, _, _)) => Data.from_bool (f1 = f2)
    | (Array (_, l1, _), Array (_, l2, _)) => Data.from_bool (Heap.eq (l1, l2))
    | (Uninitialized, _) => raise Error.Uninitialized
    | (_,Uninitialized) => raise Error.Uninitialized
    | (v1,v2) => 
      raise Error.Dynamic 
            ("cannot compare a asl;kdjfl;askjdfkl;sj " ^ value_desc v1 ^ " and a " ^ value_desc v2
             ^ " for equality")

  fun is_unit Unit = true
    | is_unit _ = false



  (* == INITIALIZATION == *)

  fun find_ty ty_defs ty =
    case ty of 
      Ast.TypeName x => (case ty_defs x of
         NONE => raise Error.Dynamic 
                  ("no definition for type variable " ^ Symbol.name x)
       | SOME ty => find_ty ty_defs ty)
    | Ast.Pointer ty => Ast.Pointer (find_ty ty_defs ty)
    | Ast.Array ty => Ast.Array (find_ty ty_defs ty)
    | _ => ty

  fun find_struct ty_defs st_defs x = 
    case st_defs x of
      NONE => raise Error.Dynamic ("struct " ^ Symbol.name x ^ " not defined")
    | SOME tys => map (fn (ty, f) => (find_ty ty_defs ty, f)) tys

  fun new_state {lookup_type, lookup_struct, lookup_fun, initial_function} =
    S{typedefs = find_ty lookup_type,
      structdefs = find_struct lookup_type lookup_struct,
      functions = lookup_fun,
      heap = Heap.new (),
      magic = (fn _ => raise Error.Internal "no function implementation"),
      stack = ref (T{fun_name = initial_function,
                     locals = [ (Symbol.empty, Symbol.empty) ],
                     caller = NONE,
                     depth = 0})}
    
  fun current_function (S{stack = ref (T{fun_name, ...}), ...}) = fun_name

  fun call_depth (S{stack = ref (T{depth, ...}), ...}) = depth


  
  (* == HEAP MANIPULATION == *)

  type addr = Heap.addr

  val fst = fn (x,_) => x
  fun get_heap_ty structdefs ty = 
    case ty of 
      Ast.Void       => raise Error.Dynamic "void types invalid on heap"
    | Ast.TypeName _ => raise Error.Internal "type variable"
    | Ast.Bool       => Heap.Bool
    | Ast.Int        => Heap.Int
    | Ast.Char       => Heap.Char
    | Ast.String     => Heap.String
    | Ast.Pointer _  => Heap.Loc
    | Ast.Array _    => Heap.Loc
    | Ast.StructName st => 
      Heap.Struct (map (get_heap_ty structdefs o fst) (structdefs st))
    | Ast.Any        => raise Error.Dynamic "dyn types cannot live on heap"

  fun offset_index (_, (loc, NONE, []), ndx) = (loc, SOME ndx, [])
    | offset_index (_, (_, SOME _, _), _) =
      raise Error.Internal "double index offset"
    | offset_index _ = 
      raise Error.Internal "field offset followed by index offset"

  fun offset_field (S{structdefs, ...}, (loc, ndx, offs), x, field) =
    let 
      fun seek_field ([], off) =
          raise Error.Dynamic 
                ("Field " ^ Symbol.name field ^ " not found in struct " 
                 ^ Symbol.name x)
        | seek_field ((ty, field') :: fields, tys) =
          (case Symbol.compare (field, field') of
             EQUAL => (Heap.offset (rev tys), ty)
           | _ => seek_field (fields, get_heap_ty structdefs ty :: tys))
      val (off, ty) = seek_field (structdefs x, [])
    in 
      (ty, (loc, ndx, offs @ [ off ]))
    end

  fun alloc (S{heap, typedefs, structdefs, ...}, ty) =
    let 
      val ty = typedefs ty
      val size_t = Heap.sizeof (get_heap_ty structdefs ty)
      val loc = Heap.alloc (heap, size_t)
    in Pointer (ty, loc) end

  fun alloc_array (S{heap, typedefs, structdefs, ...}, ty, i) =
    let 
      val ty = typedefs ty
      val size_t = Heap.sizeof (get_heap_ty structdefs ty)
      val loc = Heap.alloc_array (heap, size_t, Data.to_int i)
    in Array (ty, loc, Data.to_int i) end

  fun array_size (S{heap, ...}, (loc, NONE, [])) = Heap.size (heap, loc)
    | array_size _ = raise Error.Internal "array_size with an offset"

  fun get_addr (S{heap, typedefs, ...}, (ty, addr)) = 
    case typedefs ty of
      Ast.Void       => Unit
    | Ast.StructName st => 
      PseudoStruct (st, Heap.loc_string (Heap.get_loc (heap, addr)))
    | Ast.TypeName _ => raise Error.Internal "type variable"
    | Ast.Bool       => Bool   (Heap.get_bool   (heap, addr))
    | Ast.Int        => Int    (Heap.get_int    (heap, addr))
    | Ast.Char       => Char   (Heap.get_char   (heap, addr))
    | Ast.String     => String (Heap.get_string (heap, addr))
    | Ast.Pointer ty => Pointer (ty, Heap.get_loc (heap, addr))
    | Ast.Array ty   => 
      let val loc = Heap.get_loc (heap, addr)
      in Array (ty, loc, Heap.size (heap, loc)) end
    | Ast.Any       => raise Error.Dynamic "dyn types cannot live on heap"

  fun put_addr (S{heap, typedefs, ...}, (ty, addr), v) =
     (assert (v, typedefs ty)
      ; case v of 
           Unit            => ()
         | Int i           => Heap.put_int    (heap, addr) i
         | Bool b          => Heap.put_bool   (heap, addr) b
         | Char c          => Heap.put_char   (heap, addr) c
         | String s        => Heap.put_string (heap, addr) s
         | Function f      => raise Error.Internal "impossible"
         | PseudoStruct _  => raise Error.Internal "impossible"
         | NullPointer     => Heap.put_null   (heap, addr)
         | Pointer (_, l)  => Heap.put_loc    (heap, addr) l
         | Array (_, l, _) => Heap.put_loc    (heap, addr) l
         | Uninitialized   => raise Error.Internal "impossible")

  (* == STACK MANIPULATION == *)

  fun push_fun (S{stack = stack as ref (T{depth, ...}), ...}, f, data) =
      stack := T{fun_name = f, 
                 locals   = [ (Symbol.empty, Symbol.empty) ], 
                 caller   = SOME (data, !stack),
                 depth = depth + 1}


  fun pop_fun (S{stack, ...}) = 
    let val T{caller, ...} = !stack
    in 
      case caller of 
        NONE => NONE
      | SOME (data, caller_stack as T{fun_name,...}) =>
        (stack := caller_stack; SOME (fun_name, data))
    end

  fun push_scope (S{stack, ...}) =
    let val T{fun_name, locals, caller, depth} = !stack
    in 
      stack := T{fun_name = fun_name, 
                 locals   = (Symbol.empty, Symbol.empty) :: locals,
                 caller   = caller, 
                 depth    = depth}
    end

  fun smash_scope (state as S{stack, ...}) = 
      let val T{fun_name, locals, caller, depth} = !stack
      in case locals of
          local1 :: local2 :: locals => 
          (stack := T{fun_name = fun_name, 
                      locals   = local2 :: locals,
                      caller   = caller, 
                      depth    = depth};
           smash_scope state)
        | _ => ()
      end

  fun stacktrace (state as S{stack, ...}) = 
    let 
      fun loop (newstack as T{fun_name, locals, caller, depth}, trace) =
        case caller of 
          NONE => (stack := newstack; smash_scope state; trace)
        | SOME (data, caller_stack as T{fun_name,...}) => 
          loop (caller_stack, (fun_name, data) :: trace)
    in 
      loop (!stack, [])
    end

  fun pop_scope (_, 0) = ()
    | pop_scope (state as S{stack, ...}, n) = 
      let val T{fun_name, locals, caller, depth} = !stack
      in
        case locals of
          local1 :: local2 :: locals => 
          (stack := T{fun_name = fun_name, 
                      locals   = local2 :: locals,
                      caller   = caller, 
                      depth    = depth};
           pop_scope (state, n - 1))
        | _ => raise Error.Internal "no more scopes to pop out of"
      end

  fun clear_locals (state as S{stack, ...}) = 
     let 
       val T{fun_name, locals, caller, depth} = !stack
     in stack := T{fun_name = fun_name,
                   locals = (Symbol.empty, Symbol.empty) :: tl locals,
                   caller = caller,
                   depth = depth}
     end

  fun declare (S{stack, typedefs, ...}, x, ty) = 
    case !stack of
      T{locals = [], ...} => 
      raise Error.Internal "cannot declare a variable with no stack"
    | T{fun_name, locals = (lclT, lclV) :: locals, caller, depth} =>
      stack := T{fun_name = fun_name,
                 locals = 
                 case Symbol.look lclT x of
                   NONE =>
                   (Symbol.bind lclT (x, typedefs ty), lclV) :: locals
                 | SOME ty' =>
                   raise Error.Dynamic ("variable " ^ Symbol.name x ^ 
                                        " already declared"),
                 caller = caller,
                 depth = depth}

  fun get_locals ([], f, fs) = 
      (case fs f of
          NONE => raise Error.Dynamic ("undeclared variable " ^ Symbol.name f)
        | SOME (ty, tys) => (Ast.Any, Function (Symbol.name f, ty, tys)))
    | get_locals ((lclT, lclV) :: locals, x, fs) = 
      (case Symbol.look lclT x of
          NONE => get_locals (locals, x, fs)
        | SOME ty => 
          (case Symbol.look lclV x of 
              NONE => (ty, Uninitialized)
            | SOME v => (ty, v)))

  fun get_id (S{stack = ref (T{locals, ...}), functions, ...}, x) =
    #2 (get_locals (locals, x, functions))

(*
  fun get_ty (S{stack = ref (T{locals, ...}), functions, ...}, x) =
    #1 (get_locals (locals, x, functions))
*)

  exception Undeclared 

  fun put_stack ([], x, v) = raise Undeclared
    | put_stack ((lclT, lclV) :: locals, x, v) = 
      case Symbol.look lclT x of 
        NONE => (lclT, lclV) :: put_stack (locals, x, v)
      | SOME ty => 
        if typecheck (v, ty) 
        then (lclT, Symbol.bind lclV (x, v)) :: locals
        else raise Error.Dynamic ("assigning " ^ value_desc v ^
                                  " where a value of type " ^ Ast.Print.pp_tp ty
                                  ^ " is expected")

  fun put_id (state as S{stack, ...}, x, v) = 
    let val T{fun_name, locals, caller, depth} = !stack
    in 
      stack := T{fun_name = fun_name,
                 locals   = put_stack (locals, x, v),
                 caller   = caller,
                 depth    = depth}
      handle Undeclared => raise Error.Dynamic ("undeclared variable " ^ 
                                                Symbol.name x)
    end 

  fun local_tys (state as S{stack, ...}) =
    let 
      val T{locals, ...} = !stack
    in
       case locals of 
          [] => raise Error.Internal ("no local variables to report")
        | (lclT, _) :: _ => lclT
    end

  (* Debugging *)

  fun print_locals (S{stack = ref (T{locals, ...}), ...}) =
	let
		fun print_locals'(ty_table,v_table) = 
		let
			val s_v_list = Symbol.elemsi v_table
	  in
			List.app (fn (s,v) => TextIO.print (Symbol.name s ^ ": "^(value_string v)^"\n")) s_v_list	
   	end
	in
		case locals of nil => () | (l::llist) => print_locals' l
	end

end

