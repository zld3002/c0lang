(* Abstract data representation for Cymbol *)
(* Robert J. Simmons                       *)

signature DATA = sig

  type intrep
  type boolrep
 
  val from_bool  : bool -> boolrep
  val from_int   : Word32.word -> intrep

  (* XXX Array indices can only be as large as SML integers!*)
  val to_int     : intrep -> int   (* Used for array indices *)
  val to_bool    : boolrep -> bool (* Used for short-circuting operators *)

  (* Debugging *)
  val bool_to_string : boolrep -> string
  val int_to_string : intrep -> string

  val int_not    : intrep  -> intrep
  val bool_not   : boolrep -> boolrep
  val bit_not    : intrep  -> intrep
  val int_add    : intrep  * intrep  -> intrep
  val int_sub    : intrep  * intrep  -> intrep
  val int_mul    : intrep  * intrep  -> intrep
  val int_div    : intrep  * intrep  -> intrep
  val int_mod    : intrep  * intrep  -> intrep
  val int_bitand : intrep  * intrep  -> intrep
  val int_bitor  : intrep  * intrep  -> intrep
  val int_bitxor : intrep  * intrep  -> intrep
  val int_shiftl : intrep  * intrep  -> intrep
  val int_shiftr : intrep  * intrep  -> intrep
  val int_lt     : intrep  * intrep  -> boolrep
  val int_leq    : intrep  * intrep  -> boolrep
  val int_eq     : intrep  * intrep  -> boolrep
  val int_neq    : intrep  * intrep  -> boolrep
  val int_geq    : intrep  * intrep  -> boolrep
  val int_gt     : intrep  * intrep  -> boolrep
  val bool_and   : boolrep * boolrep -> boolrep
  val bool_or    : boolrep * boolrep -> boolrep
  val bool_eq    : boolrep * boolrep -> boolrep

end

signature CONCRETE = 
DATA where type intrep = Word32.word and type boolrep = bool

structure Concrete :> CONCRETE = struct

  type intrep = Word32.word
  type boolrep = bool

  val from_bool = fn x => x
  val from_int = fn x => x
  val to_int = Word32.toInt
  val to_bool = fn x => x

  val bool_to_string = fn true => "true" | false => "false"
  val int_to_string = Word32Signed.toString

  val int_not = fn x => Word32.-(0wx0, x)
  val bool_not = not
  val bit_not = Word32.notb
  val int_add = Word32.+
  val int_sub = Word32.-
  val int_mul = Word32.*
  val int_div = Word32Signed.quot
  val int_mod = Word32Signed.rem
  val int_bitand = Word32.andb
  val int_bitor = Word32.orb
  val int_bitxor = Word32.xorb
  val int_shiftl = fn (x, y) => Word32.<<(x, Word.fromInt(Word32.toInt y))
  val int_shiftr = fn (x, y) => Word32.>>(x, Word.fromInt(Word32.toInt y))
  val int_lt = Word32Signed.signed_less
  val int_leq = fn (x,y) => x = y orelse Word32Signed.signed_less (x, y)
  val int_eq = fn (x, y : intrep) => x = y
  val int_neq = fn (x, y : intrep) => not (x = y)
  val int_geq = Word32.>=
  val int_gt = Word32.>
  val bool_and = fn (x, y) => x andalso y
  val bool_or = fn (x, y) => x orelse y
  val bool_eq = fn (x, y) => (x andalso y) orelse (not x andalso not y)

end

