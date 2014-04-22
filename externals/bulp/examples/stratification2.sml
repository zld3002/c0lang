CM.make "../sources.cm";

signature GREEK =
sig
    datatype rel = SON of string * string
		 | DAUGHTER of string * string

    val can_marry : rel list -> string -> string -> bool
end

structure Greek :> GREEK =
struct

datatype rel = SON of string * string
	     | DAUGHTER of string * string

datatype P = S of string * string
	   | D of string * string
	   | R of string * string (*related*)
	   | CM of string * string (*can marry*)

structure Predicate : PREDICATE =
struct
structure S = Syntax
structure Eval = McAllester

type predicate = P

fun inj_arg s = S.SCONST s

fun prj_arg (S.SCONST s) = s

fun inj (S (a1, a2)) = S.P("Son", [inj_arg a1, inj_arg a2])
  | inj (D (a1, a2)) = S.P("Daughter", [inj_arg a1, inj_arg a2])
  | inj (R (a1, a2)) = S.P("Related", [inj_arg a1, inj_arg a2])
  | inj (CM (a1, a2)) = S.P("Can Marry", [inj_arg a1, inj_arg a2])

fun prj (S.P ("Son", [a1, a2])) = S (prj_arg a1, prj_arg a2)
  | prj (S.P ("Daughter", [a1, a2])) = D (prj_arg a1, prj_arg a2)
  | prj (S.P ("Related", [a1, a2])) = R (prj_arg a1, prj_arg a2)
  | prj (S.P ("Can Marry", [a1, a2])) = CM (prj_arg a1, prj_arg a2)
end

structure B = Bulp (Predicate)
(*
val prog = [
    (R (VAR "x", VAR "y"), [D (VAR "x", VAR "y")]),
    (R (VAR "x", VAR "y"), [S (VAR "x", VAR "y")]),
    (R (VAR "x", VAR "y"), [R (VAR "y", VAR "x")]), (*commutativity*)
    (R (VAR "x", VAR "z"), [R (VAR "x", VAR "y"), R (VAR "y", VAR "z")]), (*transitivity*)
    (CM (VAR "x", VAR "y"), [S(VAR "x", VAR "a"), D (VAR "y", VAR "b"), NOT (R (VAR "x", VAR "y"))]),
    (CM (VAR "x", VAR "y"), [CM (VAR "y", VAR "x")])
]

fun make_input [] = []
  | make_input (SON (s1, s2) :: L) = S (NAME s1, NAME s2) :: (make_input L)
  | make_input (DAUGHTER (s1, s2) :: L) = D (NAME s1, NAME s2) :: (make_input L)

fun can_marry r n1 n2 = 
    let
	val db = valOf (B.new prog)
	val _ = B.add db (make_input r)
	val _ = B.saturate db
    in
	B.query db (CM (NAME n1, NAME n2)) = []
    end*)
val t = D ("a", "b") : B.predicate

end
    
