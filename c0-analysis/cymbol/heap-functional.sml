functor FunctionalHeapFn (structure Data : DATA
                          val default_bool : Data.bool_rep
                          val default_int  : Data.int_rep
                          val default_char : char) :>
   HEAP where type bool_rep = Data.bool_rep
          and type int_rep = Data.int_rep 
          and type char_rep = char  = struct

  type bool_rep = Data.bool_rep
  type int_rep = Data.int_rep
  type char_rep = char
  type string_rep = string
  type native_pointer = MLton.Pointer.t
  fun rep_to_str x = x
  fun str_to_rep x = x 

  (* All errors raised by this implementation are catastrophic *)
  val unsafe = fn () => raise Error.Internal "Unsafe memory access"

  (* Nothing special is done about representing types *)
  datatype ty = Bool | Int | Char | String | Loc | Struct of ty list
  type size_t = ty
  val sizeof = fn x => x

  (* The heap is a recusive tagged structure mimicing structures *)
  datatype loc = Null | Local of int | Native of MLton.Pointer.t
  datatype mem 
    = B of bool_rep 
    | I of int_rep  
    | C of char_rep
    | S of string
    | L of loc
    | T of mem vector

  fun default_mem ty =
    case ty of
      Bool       => B default_bool
    | Int        => I default_int
    | Char       => C default_char
    | String     => S ""
    | Loc        => L Null
    | Struct tys => T (Vector.fromList (List.map default_mem tys))

  structure M = 
  SplayMapFn(struct type ord_key = int val compare = Int.compare end)
  datatype alloc = One of mem | Some of int * mem M.map
  type heap = alloc GrowArray.growarray
  val new : unit -> heap = GrowArray.empty

  (* Locations are simply indices into the heap's growable array *)
  type offset = ty list
  type addr = loc * int option * offset list
  val offset = fn x => x
  fun loc_string Null = "NULL"
    | loc_string (Local l) =
      "loc0x" ^ Word.toString (0wx10000 + Word.fromInt l)
    | loc_string (Native p) =
      "nat0x" ^ Word.toString (MLton.Pointer.diff (MLton.Pointer.null, p))

  fun size (heap, Null) = 0
    | size (heap, Native ptr) = 
      raise Error.Internal "don't know size of native pointers"
    | size (heap, Local loc) = 
      case GrowArray.sub heap loc of
        Some (i, ms) => i
      | One _ => unsafe ()
      

  fun null n = n = Null

  fun eq (i, j : loc) = i = j

  (* Allocation *)

  fun allocate (heap,  m) = 
    let val loc = GrowArray.length heap
    in GrowArray.update heap loc m; Local loc end

  fun alloc (heap, ty) =
    allocate (heap, One (default_mem ty ))

  fun tabulate (n, f) =
    let fun loop m x = if m = n then x else loop (m + 1) (M.insert (x, m, f m))
    in loop 0 M.empty end

  fun alloc_array (heap, ty, n) =
    let val default = default_mem ty
    in allocate (heap, Some (n, tabulate (n, fn _ => default))) end

  (* Reading *)
  
  fun getmem (m, []) : mem = m
    | getmem (T ms, off :: offs) = getmem (Vector.sub (ms, length off), offs)
    | getmem _ = unsafe ()
  fun get (_, (Null, _, _)) = unsafe ()
    | get (_, (Native _, _, _)) =
      raise Error.Internal "cannot read from native pointers"
    | get (heap : heap, (Local loc, sub, offs) : addr) = 
      case (sub, GrowArray.sub heap loc) of
        (NONE, One m) => getmem (m, offs)
      | (SOME ndx, Some (_, ms)) => getmem (M.lookup (ms, ndx), offs)
      | _ => unsafe ()

  val get_bool   = (fn B b => b | _ => unsafe ()) o get
  val get_int    = (fn I i => i | _ => unsafe ()) o get
  val get_char   = (fn C c => c | _ => unsafe ()) o get
  val get_string = (fn S s => s | _ => unsafe ()) o get
  val get_loc    = (fn L l => l | _ => unsafe ()) o get

  (* Writing *)

  fun putmem (B _, []) (B b) = B b
    | putmem (I _, []) (I i) = I i
    | putmem (C _, []) (C c) = C c
    | putmem (S _, []) (S s) = S s
    | putmem (L _, []) (L l) = L l
    | putmem (T mem, off :: offs) m = 
      let 
        val newmem = putmem (Vector.sub (mem, length off), offs) m
      in T (Vector.update (mem, length off, newmem)) end
    | putmem _ _ = unsafe ()

  fun put (heap, (Null, _, _)) _ = unsafe ()
    | put (heap, (Native _, _, _)) _ =
      raise Error.Internal "cannot write to native pointers"
    | put (heap, (Local loc, sub, offs)) m =
      case (sub, GrowArray.sub heap loc) of
        (NONE, One oldmem) => 
        GrowArray.update heap loc (One (putmem (oldmem, offs) m))
      | (SOME ndx, Some (n, oldmems)) => 
        let 
          val newmem = putmem (M.lookup (oldmems, ndx), offs) m
          val newmems = M.insert (oldmems, ndx, newmem)
        in GrowArray.update heap loc (Some (n, newmems)) end
      | _ => unsafe ()

  val put_bool   = fn x => put x o B 
  val put_int    = fn x => put x o I
  val put_char   = fn x => put x o C 
  val put_string = fn x => put x o S 
  val put_loc    = fn x => put x o L 
  val put_null   = fn x => put x (L Null)

  val to_native =
   fn Null => MLton.Pointer.null
    | Local _ => raise Error.Internal "cannot turn local pointers into native"
    | Native ptr => ptr

  val from_native =
   fn ptr => 
      if EQUAL = MLton.Pointer.compare (ptr, MLton.Pointer.null)
      then Null else Native ptr

  fun str_to_native _ = raise Error.Internal "unimplemented"
  fun native_to_str _ = raise Error.Internal "unimplemented" 

  (* Checkpointing *)
  type checkpoint = alloc vector
  fun checkpoint heap =
      Vector.tabulate (GrowArray.length heap, fn i => GrowArray.sub heap i)
  fun restore (heap, checkpoint) = 
      Vector.appi (fn (i, alloc) => GrowArray.update heap i alloc) checkpoint
 
end 

structure ConcreteFunctionalHeap = FunctionalHeapFn 
  (structure Data = ConcreteData
   val default_bool = false
   val default_int  = Word32.fromInt 0
   val default_char = #"\^@")
