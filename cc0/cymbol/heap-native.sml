functor NativeHeapFn (structure Data : CONCRETE_DATA
                      val default_bool : Data.bool_rep
                      val default_int  : Data.int_rep
                      val default_char : char
                      val default_string : string) :>
   HEAP where type bool_rep = Data.bool_rep
          and type int_rep = Data.int_rep 
          and type char_rep = char  
          and type native_pointer = MLton.Pointer.t = struct

  type bool_rep = Data.bool_rep
  type int_rep = Data.int_rep
  type char_rep = char
  type string_rep = MLton.Pointer.t
  type native_pointer = MLton.Pointer.t

  (* Internalization of strings *)
  val prim_make_c0_string =
     _import "c0_string_fromcstr" : string -> MLton.Pointer.t;
  fun make_c0_string s = prim_make_c0_string (s ^ "\000")
  
  structure StringTab = Symtab (type entrytp = MLton.Pointer.t)
  fun str_to_rep str = 
     let val s = Symbol.symbol str in
        case StringTab.lookup s of
         NONE => 
         let val ptr = make_c0_string str
         in StringTab.bind (s, ptr); ptr end
       | SOME ptr => ptr
     end

  fun rep_to_str' s ptr = 
     let val c = Byte.byteToChar (MLton.Pointer.getWord8 (ptr, 0))
     in 
        if c = #"\000" then implode (rev s)
        else rep_to_str' (c :: s) (MLton.Pointer.add (ptr, 0wx1))
     end
  fun rep_to_str ptr = 
     if MLton.Pointer.null = ptr then ""
     else rep_to_str' [] ptr

  (* The native interface need only deal with NULL being represented as NONE *)
  type ptr = MLton.Pointer.t 
  val null_ptr = fn ptr => ptr = MLton.Pointer.null
  fun from_native ptr = if null_ptr ptr then NONE else SOME ptr
  fun to_native NONE = MLton.Pointer.null
    | to_native (SOME ptr) = ptr
  val str_to_native = fn ptr => ptr
  val native_to_str = fn ptr => ptr

  (* Internal representation of sizes and locations *)
  datatype ty = Bool | Int | Char | String | Loc | Struct of ty list

  val sizeof_bool = (_import "sizeof_bool"    : unit -> int;) ()
  val sizeof_int  = (_import "sizeof_int"     : unit -> int;) ()
  val sizeof_char = (_import "sizeof_char"    : unit -> int;) ()
  val sizeof_ptr  = (_import "sizeof_ptr"     : unit -> int;) ()
  
  type size_t = int
  fun sizeof ty = 
    case ty of 
      Bool   => sizeof_bool
    | Int    => sizeof_int
    | Char   => sizeof_char
    | String => sizeof_ptr
    | Loc    => sizeof_ptr
    | Struct tys => foldr (op +) 0 (map sizeof tys)

  type loc = ptr option
  fun loc_string NONE = "NULL"
    | loc_string (SOME ptr) = 
      "0x" ^ Word.toString (MLton.Pointer.diff (MLton.Pointer.null, ptr))

  (* Allocation *)
  type heap = unit  

  val new = fn () => ()

  val alloc_ = _import "c0_alloc" : int -> ptr;
  fun alloc ((), size) = 
    let val ptr = alloc_ size 
    in 
      (* print ("alloc of " ^ Int.toString size); *)
      if null_ptr ptr then raise Error.Allocation else SOME ptr 
    end 

  val array_alloc_ = _import "c0_array_alloc" : int * int -> ptr;
  fun alloc_array ((), size, n) =
    let val ptr = array_alloc_ (size, n) 
    in
      (* print ("alloc_array of " ^ Int.toString size ^ " with ");
      print (Int.toString n ^ " elements.\n"); *)
      if null_ptr ptr then raise Error.Allocation else SOME ptr 
    end
  
  (* Pointers and stuff *)
  val size_ = _import "c0_array_length" : ptr -> int;
  fun size ((), NONE) = 0
    | size ((), SOME ptr) = size_ ptr

  val null = not o Option.isSome

  val eq : loc * loc -> bool = fn (x, y) => x = y

  (* Offsets *)
  type offset = Word32.word
  type addr = loc * int option * offset list

  fun offset (tys : ty list) : Word32.word = 
    foldr (fn (x, y) => x + y) 0wx0 (map (Word32.fromInt o sizeof) tys)

  val array_sub = _import "c0_array_sub" : ptr * int * int -> ptr;  
  fun addr_sub (NONE, _, off) = raise Error.Internal "offset of null pointer"
    | addr_sub (SOME ptr, NONE, offs) =
      let
        val ptr'' = MLton.Pointer.add (ptr, foldr Word32.+ 0wx0 offs)
      in
        ptr''
      end
    | addr_sub (SOME ptr, SOME ndx, offs) = 
      let 
	(* XXX ZERO IS INSANE IF IT'S ANYTHING BUT THE BARE RUNTIME *)
        val ptr'  = array_sub (ptr, ndx, 0) 
        val ptr'' = MLton.Pointer.add (ptr', foldr Word32.+ 0wx0 offs)
      in
        (* print ("Array offset! Index = " ^ Int.toString ndx ^ "\n");
        print ("Item size:           " ^ Int.toString (array_elt_ ptr) ^ "\n");
        print ("before offset:       " ^ loc_string (SOME ptr) ^ "\n");
        print ("after array offset:  " ^ loc_string (SOME ptr') ^ "\n");
        print ("after struct offset: " ^ loc_string (SOME ptr'') ^ "\n"); *)
        ptr''
      end

  fun get1 addr = MLton.Pointer.getWord8  (addr_sub addr, 0)
  fun get4 addr = MLton.Pointer.getWord32 (addr_sub addr, 0)
  fun get8 addr = MLton.Pointer.getWord64 (addr_sub addr, 0)
  fun getP addr = 
    from_native (MLton.Pointer.getPointer (addr_sub addr, 0))

  fun put1 (addr, x) = MLton.Pointer.setWord8   (addr_sub addr, 0, x)
  fun put4 (addr, x) = MLton.Pointer.setWord32  (addr_sub addr, 0, x)
  fun put8 (addr, x) = MLton.Pointer.setWord64  (addr_sub addr, 0, x)
  fun putP (addr, x) = 
    (MLton.Pointer.setPointer (addr_sub addr, 0, to_native x))

  fun badsize n s = 
    raise Error.Internal ("unsupported " ^ Int.toString n ^ "-byte " ^ s)

  val (get_bool, put_bool) =
    if sizeof_bool = 1 then 
      (fn ((), addr) => 0wx0 <> get1 addr,
       fn ((), addr) =>
       fn x => if x then put1 (addr, 0wx1) else put1 (addr, 0wx0))
    else if sizeof_bool = 4 then 
      (fn ((), addr) => 0wx0 <> get4 addr,
       fn ((), addr) => 
       fn x => if x then put4 (addr, 0wx1) else put4 (addr, 0wx0))
    else badsize sizeof_bool "bool"
    
  val (get_int, put_int) = 
    if sizeof_int = 4 then 
      (fn ((), addr) => get4 addr, 
       fn ((), addr) => fn x => put4 (addr, x))
    else badsize sizeof_int "int"

  val (get_char, put_char) = 
    if sizeof_char = 1 then 
      (fn ((), addr) => Byte.byteToChar (get1 addr),
       fn ((), addr) => fn c => put1 (addr, Byte.charToByte c))
    else badsize sizeof_char "char"

  val (get_string, put_string) = 
   (fn ((), addr) => MLton.Pointer.getPointer (addr_sub addr, 0),
    fn ((), addr) => 
    fn char_ptr => 
       MLton.Pointer.setPointer (addr_sub addr, 0, char_ptr))

  val (get_loc, put_loc) =
    (fn ((), addr) => getP addr,
     fn ((), addr) => fn ptr => putP (addr, ptr))

  val put_null = fn ((), addr) => putP (addr, NONE)


  (* XXX TODO SOMETHING LESS TOTALLY BOGUS *)
  type checkpoint = unit
  val checkpoint = fn _ => ()
  val restore    = fn _ => ()

end

structure ConcreteNativeHeap = NativeHeapFn 
  (structure Data = ConcreteData
   val default_bool = false
   val default_int  = Word32.fromInt 0
   val default_char = #"\^@"
   val default_string = "")

(*
  _alloc_bigass_array_to_begin
  _c0_sizeof_pointer (* WARNING DEAL WITH SIZE_T ISSUES *)

  (* _c0_abort will raise sigabrt *)
  _c0_alloc (* may segfault, but will otherwise return a MLton.Pointer.t *)
  _c0_array_alloc (* same *)
  _c0_array_sub (* won't segfault if you check the length you moron *)
  _c0_array_length (* you moron *)
  _c0_string_empty (* Doesn't allocate *) 
  _c0_string_length (* Doesn't allocate *)
  _c0_string_charat (* *)
  _
*)
