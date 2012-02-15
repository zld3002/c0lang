(* Concrete-only, imperative heap structure, intended to be compatible
 * with Standard ML of New Jersey in a very MLton-centric project *)

functor ImperativeHeapFn (structure Data : CONCRETE_DATA) :>
   HEAP where type bool_rep = Data.bool_rep
          and type int_rep = Data.int_rep 
          and type char_rep = char = 
struct

  (* Strings are internalized and referred to by their index *)
  structure Strings = 
  SplayMapFn(struct type ord_key = string val compare = String.compare end)
  local
     val strings_map: int Strings.map ref = ref Strings.empty
     val strings_index: string GrowArray.growarray = GrowArray.empty ()
  in
     fun str_to_rep s = 
        case Strings.find (!strings_map, s) of
           SOME rep => rep
         | NONE =>
           let val rep = GrowArray.length strings_index
           in
            ( strings_map := Strings.insert (!strings_map, s, rep)
            ; GrowArray.append strings_index s
            ; rep)
           end

     fun rep_to_str rep = GrowArray.sub strings_index rep

     val default_string_rep = str_to_rep ""
  end 
  
  type bool_rep = Data.bool_rep
  type int_rep = Data.int_rep
  type char_rep = char
  type string_rep = int
  type native_pointer = int

  (* Casting to and from Word32 *)
  fun from_bool b: Word32.word = if b then 0wx1 else 0wx0
  fun from_int i: Word32.word = i
  fun from_char c: Word32.word = Word32.fromInt (Char.ord c)
  fun from_string rep: Word32.word = Word32.fromInt rep
  fun from_loc l: Word32.word = Word32.fromInt l

  fun to_bool (x: Word32.word) = 0wx0 <> x
  fun to_int (x: Word32.word) = x
  fun to_char (x: Word32.word) = Char.chr (Word32.toInt x)
  fun to_string (x: Word32.word) = Word32.toInt x
  fun to_loc (x: Word32.word) = Word32.toInt x

  fun str_to_native x = x
  fun native_to_str x = x

  (* All types are stored in the Word32.word type *)
  datatype ty = Bool | Int | Char | String | Loc | Struct of ty list
  type size_t = int
  val sum = foldr (op +) 0
  fun sizeof (Struct tys) = offset tys
    | sizeof _ = 1
  and offset tys = sum (map sizeof tys)

  (* Allocation in the memory model *)
  type loc = int
  fun loc_string l = 
     "0x"^(Word32.toString(0wxFF4FFFA0 - Word32.fromInt l * 0wx10))

  type heap = Word32.word GrowArray.growarray

  val default: Word32.word = 0wx0

  fun new () =
  let val arr = GrowArray.empty () 
  in GrowArray.append arr default; arr end

  fun empty_mem (arr, 0) = ()
    | empty_mem (arr, i) = 
         (GrowArray.append arr default; empty_mem (arr, i-1))

  (* Every allocation is the same size *)
  fun alloc (arr, size_t) = 
     GrowArray.length arr 
     before empty_mem (arr, size_t)

  (* An array is: [ elem_size, num_elems, elem1, elem2, elem3, ... ] *)
  fun alloc_array (arr, size_t, elems) =
     GrowArray.length arr 
     before 
      ( GrowArray.append arr (Word32.fromInt size_t)
      ; GrowArray.append arr (Word32.fromInt elems)
      ; empty_mem (arr, size_t * elems))

  fun null l = l = 0
  fun eq (l1: loc, l2: loc) = l1 = l2
  fun size (arr, l) = 
     if null l then 0
     else Word32.toInt (GrowArray.sub arr (l+1))

  (* Offsets and array dereferencing *)
  type offset = int
  type addr = loc * int option * offset list

  fun getaddr arr (i, NONE, offs) = i + sum offs
    | getaddr arr (i, SOME ndx, offs) = 
        i + 2 + (Data.to_int (GrowArray.sub arr i) * ndx) + sum offs

  (* Native interface is pretty trivial in this case *)
  fun to_native i = i
  fun from_native i = i

  (* Reading *)
  fun get (arr, addr) = GrowArray.sub arr (getaddr arr addr)

  val get_bool =   to_bool o get
  val get_int =    to_int o get
  val get_char =   to_char o get
  val get_string = to_string o get
  val get_loc =    to_string o get
 
  (* Writing *)
  fun put arr addr v = GrowArray.update arr (getaddr arr addr) v
 
  fun put_bool (arr, addr) b =   put arr addr (from_bool b)
  fun put_int (arr, addr) i =    put arr addr (from_int i)
  fun put_char (arr, addr) c =   put arr addr (from_char c)
  fun put_string (arr, addr) s = put arr addr (from_string s)
  fun put_loc (arr, addr) l =    put arr addr (from_loc l)
  fun put_null (arr, addr) =     put arr addr (from_loc 0)

  (* Checkpointing *)
  type checkpoint = Word32.word vector
  fun checkpoint arr =
      Vector.tabulate (GrowArray.length arr, fn i => GrowArray.sub arr i)
  fun restore (arr, checkpoint) = 
      Vector.appi (fn (i, alloc) => GrowArray.update arr i alloc) checkpoint
end

structure ConcreteImperativeHeap = ImperativeHeapFn
  (structure Data = ConcreteData)
