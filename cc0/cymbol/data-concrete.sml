(* Abstract data representation for Cymbol *)
(* Robert J. Simmons                       *)

structure ConcreteData :> CONCRETE_DATA = struct

  type int_rep = Word32.word
  type bool_rep = bool

  val from_bool = fn x => x
  val from_int = fn x => x
  val to_int = Word32.toIntX 
  val to_bool = fn x => x

  val bool_to_string = fn true => "true" | false => "false"
  val int_to_string = Word32Signed.toString

  fun mask_shift_5 x =
     if Word32.>(x, 0wx1F) then raise Div
     else Word.fromInt(Word32.toInt x)

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
  val int_shiftl = fn (x, y) => Word32.<<(x, mask_shift_5 y)
  val int_shiftr = fn (x, y) => Word32.~>>(x, mask_shift_5 y)
  val int_lt =     fn (x, y) => Word32Signed.signed_less (x, y)
  val int_leq =    fn (x, y) => x = y orelse Word32Signed.signed_less (x, y)
  val int_eq =     fn (x, y : int_rep) => x = y
  val int_neq =    fn (x, y : int_rep) => not (x = y)
  val int_geq =    fn (x, y) => x = y orelse Word32Signed.signed_less (y, x)
  val int_gt =     fn (x, y) => Word32Signed.signed_less (y, x)
  val bool_and =   fn (x, y) => x andalso y
  val bool_or =    fn (x, y) => x orelse y
  val bool_eq =    fn (x, y) => (x andalso y) orelse (not x andalso not y)

end

