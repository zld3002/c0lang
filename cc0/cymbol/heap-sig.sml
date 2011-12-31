(* Heaps are the basic wrapper around memory representations.                *)
(* Allocation in a heap may raise Error.Allocation, but this should be the   *)
(* *ONLY* non-catastrophic error raised by an implementation of HEAP.        *)
(* Heaps may be implemented in a manner that breaks interface boundaries,    *)
(* and as a result it is the obligation of the user of the heap to check for *)
(* null pointers/array out-of-bounds before accessing the heap.              *)

signature HEAP = sig

  type bool_rep
  type int_rep
  type char_rep
  type string_rep
  type native_pointer

  (* Types in the heap are essentially abstractions of sizes      *)
  (* Both arrays and pointers should be interpreted as "Loc"      *)
  (* Note: this requires awareness of order within structs.       *)
  datatype ty = Bool | Int | Char | String | Loc | Struct of ty list

  (* Allocation uses the internal representation of types, size_t *)
  type size_t
  val sizeof : ty -> size_t

  type loc
  val loc_string : loc -> string (* DEBUGGING ONLY *)

  (* Native interface *)
  val to_native   : loc -> native_pointer
  val from_native : native_pointer -> loc
  val str_to_native : string_rep -> native_pointer
  val native_to_str : native_pointer -> string_rep

  (* The allocation functions may raise Error.Allocation,         *)
  (* but never return a null pointer                              *)
  type heap
  val new : unit -> heap
  val alloc : heap * size_t -> loc
  val alloc_array : heap * size_t * int -> loc

  (* Size will safely return 0 given a null pointer               *)
  val size : heap * loc -> int 
  val null : loc -> bool
  val eq : loc * loc -> bool

  (* Heap access uses a root pointer, an array offset,            *)
  (* and the internal representation of struct offsets.           *)
  type offset 
  type addr = loc * int option * offset list
  val offset : ty list -> offset

  (* Strings *)
  val str_to_rep : string -> string_rep
  val rep_to_str : string_rep -> string

  (* Reading *)
  val get_bool   : heap * addr -> bool_rep
  val get_int    : heap * addr -> int_rep
  val get_char   : heap * addr -> char_rep
  val get_string : heap * addr -> string_rep
  val get_loc    : heap * addr -> loc

  (* Writing *)
  val put_bool   : heap * addr -> bool_rep   -> unit
  val put_int    : heap * addr -> int_rep    -> unit
  val put_char   : heap * addr -> char_rep   -> unit
  val put_string : heap * addr -> string_rep -> unit
  val put_loc    : heap * addr -> loc        -> unit
  val put_null   : heap * addr -> unit 

  (* Checkpointing *)
  type checkpoint 
  val checkpoint : heap -> checkpoint
  val restore : heap * checkpoint -> unit

end

