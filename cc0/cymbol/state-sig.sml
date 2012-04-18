(* Unified state for Cymbol *)
(* Relies on compiler (Ast) types and Symbol.symbol identifiers *)
(* Robert J. Simmons *)

signature STATE = sig

  type 'a state
  type value
  type bool_rep
  type int_rep
  type native_pointer
  type addr

  val new_state : 
      {lookup_type : Symbol.symbol -> Ast.tp option,
       lookup_struct : Symbol.symbol -> (Ast.tp * Symbol.symbol) list option,
       lookup_fun : Symbol.symbol -> (Ast.tp * Ast.tp list) option,
       initial_function : Symbol.symbol} -> 'a state
  val current_function : 'a state -> Symbol.symbol
  val call_depth : 'a state -> int

  (* States can be checkpointed: this is lightweight if the underlying     *)
  (* data structure is quite functional, and heavyweight otherwise!        *)
  (* You should only ever restore to the (evolved) state you checkpointed. *)
  type 'a checkpoint
  val checkpoint   : 'a state -> 'a checkpoint
  val restore      : 'a state * 'a checkpoint -> unit 
  
  (* Native interface *)
  val to_native     : addr -> native_pointer
  val from_native   : native_pointer -> addr

  (* Dynamically tagged values *)
  val int            : int_rep       -> value
  val bool           : bool_rep      -> value
  val char           : char          -> value
  val string         : string        -> value

  (* NOTE: the types passed to pointer and array must be free of type names *)
  val pointer        : Ast.tp * addr  -> value
  val array          : Ast.tp * addr * int -> value
  val null           : value
  val unit           : value
  val to_int         : value         -> int_rep
  val to_bool        : value         -> bool_rep
  val to_char        : value         -> char
  val to_string      : value         -> string
  val to_function    : value         -> string
  val to_pointer     : value         -> (Ast.tp * addr) option
  val to_array       : value         -> Ast.tp * addr * int
  val value_eq       : value * value -> bool_rep
  val value_lt       : value * value -> bool_rep
  val is_unit        : value         -> bool

  (* Heap manipulation *)
  val offset_index   : 'a state * addr * int -> addr
  val offset_field   : 'a state * addr * Symbol.symbol * Symbol.symbol
                              -> (Ast.tp * addr)
  val alloc          : 'a state * Ast.tp -> value
  val alloc_array    : 'a state * Ast.tp * int_rep -> value
  val get_addr       : 'a state * (Ast.tp * addr) -> value
  val put_addr       : 'a state * (Ast.tp * addr) * value -> unit
  val array_size     : 'a state * addr -> int

  (* Stack manipulation *)
  val push_fun       : 'a state * Symbol.symbol * 'a -> unit
  val pop_fun        : 'a state -> (Symbol.symbol * 'a) option
  val push_scope     : 'a state -> unit
  val pop_scope      : 'a state * int -> unit
  val declare        : 'a state * Symbol.symbol * Ast.tp -> unit
  val get_id         : 'a state * Symbol.symbol -> value
  (* val get_ty         : 'a state * Symbol.symbol -> Ast.tp *)
  val put_id         : 'a state * Symbol.symbol * value -> unit
  (* Gets the most-recently-in-scope types *)
  val local_tys      : 'a state -> Ast.tp Symbol.table

  (* Pop "all the way out" of functions and scopes *)
  val stacktrace     : 'a state -> (Symbol.symbol * 'a) list 
  (* Wipes out the current level of local variables *)
  val clear_locals   : 'a state -> unit

  (* Debugging *)
  val value_string   : value -> string
  val print_locals   : 'a state -> unit 

  val addr_string    : addr -> string
(*

  (* Heap allocated storage *)
  val get_addr     : 'a state * addr -> value
  val put_addr     : 'a state * addr * value -> 'a state

  (* Address offsets *)

  (* Debugging *)

  val print_state  : 'a state -> unit
  val value_string : value   -> string
*)

end

signature CONCRETE_STATE = 
STATE where type int_rep = Word32.word and type bool_rep = bool

