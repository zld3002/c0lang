(* C0 Compiler
 * Utilities for signed modular arithmetic
 * Author: Frank Pfenning
 *)

(*
 * There are two useful structure in the SML Basis Library
 * Int32, with 2's complement arithmetic,
 *        but it raises Overflow instead of doing modular arithmetic
 * Word32, with unsigned modular arithmetic
 *
 * This structure implements some signed operations on Word32
 *)

signature WORD32_SIGNED =
sig
  val TMAX : Word32.word	(* largest signed positive word, 2^31-1  *)
  val TMIN : Word32.word	(* smallest signed negative word -2^31 *)
  val ZERO : Word32.word	(* 0 *)
  val fromString : string -> Word32.word option	(* parse from string, no sign *)
				(* raises Overflow if not 0 <= n < 2^32 *)
  val fromHexString : string -> Word32.word option (* parse from string, no sign *)
				(* raises Overflow if not 0 <= n < 2^32 *)
  val toString : Word32.word -> string (* print to string, with sign *)

  (* the rest is needed only for evaluation or optimization *)

  (* quot truncates towards 0, rem(i,j) has the same sign as i *)
  (* quot and rem will raise Div if j = 0 *)
  (* quot and rem will raise Overflow if i = TMIN and j = -1 *)
  val quot : Word32.word * Word32.word -> Word32.word (* signed division *)
  val rem : Word32.word * Word32.word -> Word32.word (* signed remainder *)

  val signed_less : Word32.word * Word32.word -> bool
end

structure Word32Signed :> WORD32_SIGNED =
struct
  val TMIN = Word32.<<(Word32.fromInt(1), Word.fromInt(Word32.wordSize-1))
  val TMAX = Word32.-(TMIN, Word32.fromInt(1))
  val ZERO = Word32.fromInt(0)
  fun neg w = Word32.>(w, TMAX)

  (* fromString does not allow leading "-" *)
  fun fromString (str) =
         (* scanString might also raise Overflow *)
      let
	  val wOpt = StringCvt.scanString (Word32.scan StringCvt.DEC) str
	  val _ = case wOpt
		   of SOME(w) => if neg w andalso w <> TMIN
				 then raise Overflow
				 else ()
		    | NONE => ()
      in
	  wOpt
      end

  fun fromHexString (str) =
         (* scanString might also raise Overflow *)
	 StringCvt.scanString (Word32.scan StringCvt.HEX) str

  fun toString (w) =
      if neg w
	 then "-" ^ Word32.fmt StringCvt.DEC (Word32.~(w))
      else Word32.fmt StringCvt.DEC w

  fun quot (w1, w2) =
      if w1 = TMIN andalso w2 = Word32.fromInt(~1)
      then raise Div
      else case (neg w1, neg w2)
             of (true, true) => Word32.div(Word32.~ w1,Word32.~ w2)
              | (true, false) => Word32.~ (Word32.div(Word32.~ w1, w2))
              | (false, true) => Word32.~ (Word32.div(w1, Word32.~ w2))
              | (false, false) => Word32.div(w1, w2)

  fun rem (w1, w2) =
      if w1 = TMIN andalso w2 = Word32.fromInt(~1)
      then raise Div
      else case (neg w1, neg w2)
             of (true, true) => Word32.~ (Word32.mod(Word32.~ w1,Word32.~ w2))
              | (true, false) => Word32.~ (Word32.mod(Word32.~ w1, w2))
              | (false, true) => Word32.mod(w1, Word32.~ w2)
              | (false, false) => Word32.mod(w1, w2)

  fun signed_less (w1, w2) =
      case (neg w1, neg w2)
        of (true, true) => Word32.<(w1,w2)
         | (true, false) => true
         | (false, true) => false
         | (false, false) => Word32.<(w1,w2)
end
