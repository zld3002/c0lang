(* Abstract data representation for Cymbol *)
(* Robert J. Simmons                       *)

signature DATA = sig

  type int_rep
  type bool_rep
 
  val from_bool  : bool -> bool_rep
  val from_int   : Word32.word -> int_rep

  val to_int     : int_rep -> int   (* Used for array indices *)
  val to_bool    : bool_rep -> bool (* Used for short-circuting operators *)

  (* Debugging *)
  val bool_to_string : bool_rep -> string
  val int_to_string : int_rep -> string

  (* Options *)
  val int_not    : int_rep  -> int_rep
  val bool_not   : bool_rep -> bool_rep
  val bit_not    : int_rep  -> int_rep
  val int_add    : int_rep  * int_rep  -> int_rep
  val int_sub    : int_rep  * int_rep  -> int_rep
  val int_mul    : int_rep  * int_rep  -> int_rep
  val int_div    : int_rep  * int_rep  -> int_rep
  val int_mod    : int_rep  * int_rep  -> int_rep
  val int_bitand : int_rep  * int_rep  -> int_rep
  val int_bitor  : int_rep  * int_rep  -> int_rep
  val int_bitxor : int_rep  * int_rep  -> int_rep
  val int_shiftl : int_rep  * int_rep  -> int_rep
  val int_shiftr : int_rep  * int_rep  -> int_rep
  val int_lt     : int_rep  * int_rep  -> bool_rep
  val int_leq    : int_rep  * int_rep  -> bool_rep
  val int_eq     : int_rep  * int_rep  -> bool_rep
  val int_neq    : int_rep  * int_rep  -> bool_rep
  val int_geq    : int_rep  * int_rep  -> bool_rep
  val int_gt     : int_rep  * int_rep  -> bool_rep
  val bool_and   : bool_rep * bool_rep -> bool_rep
  val bool_or    : bool_rep * bool_rep -> bool_rep
  val bool_eq    : bool_rep * bool_rep -> bool_rep

end

signature CONCRETE_DATA = 
DATA where type int_rep = Word32.word and type bool_rep = bool

