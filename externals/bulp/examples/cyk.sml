CM.make "../sources.cm";

signature CYK = 
sig
    datatype rule = UN of string * char (*Terminal (unary) productions*)
		  | BIN of string * string * string (*Non-terminal (binary) productions*)

    type grammar = rule list

    val produces : grammar -> string -> string list (*list of all non-terminals that can produce the given string*)
    val can_produce : grammar -> string -> string -> bool (*1st string non-terminal, 2nd is input string*)
end

structure Cyk :> CYK =
struct
datatype rule = UN of string * char
	      | BIN of string * string * string

type grammar = rule list

datatype predicate = T of string * string
		   | NT of string * string * string
		   | PROD of string * int * int
		   | IN of int * string
		   | SUCC of int * int

structure Predicate : PREDICATE= 
struct 
structure S = Syntax

type predicate = predicate

fun inj_s s = 
    (case Int.fromString s of
	 NONE => S.SCONST s
       | SOME i => if i < 0 then S.VAR s else S.SCONST s
    )
fun inj_i i = if i < 0 then S.VAR (Int.toString i) else S.ICONST i

fun prj_s (S.SCONST s) = s
fun prj_i (S.ICONST i) = i

fun inj (T (X, a)) = S.P("T", [inj_s X, inj_s a])
  | inj (NT (X, A, B)) = S.P("NT", [inj_s X, inj_s A, inj_s B])
  | inj (PROD (X, i, j)) = S.P("PROD", [inj_s X, inj_i i, inj_i j])
  | inj (IN (i, a)) = S.P("IN", [inj_i i, inj_s a])
  | inj (SUCC (i, j)) = S.P("SUCC", [inj_i i, inj_i j])

fun prj (S.P("T", [X, a])) = T (prj_s X, prj_s a)
  | prj (S.P("NT", [X, A, B])) = NT(prj_s X, prj_s A, prj_s B)
  | prj (S.P("PROD", [X, i, j])) = PROD(prj_s X, prj_i i, prj_i j)
  | prj (S.P("IN", [i, a])) = IN(prj_i i, prj_s a)
  | prj (S.P("SUCC", [i, j])) = SUCC(prj_i i, prj_i j)
end

structure B = Bulp (Predicate)

val prog = 
    [(PROD ("~1", ~2, ~2), [T ("~1", "~3"), IN (~2, "~3")]),
     (PROD ("~1", ~2, ~3), [NT ("~1", "~4", "~5"), 
			    PROD ("~4", ~2, ~6),
			    PROD ("~5", ~7, ~3),
			    SUCC (~6, ~7)])
    ] : B.program

fun parse_rule (UN (X, a)) = T (X, Char.toString a)
  | parse_rule (BIN (X, A, B)) = NT(X, A, B)

fun make_succ 0 = []
  | make_succ 1 = []
  | make_succ n = SUCC(n-1, n) :: (make_succ (n-1))

fun make_input [] _ = []
  | make_input (a::S) i = IN(i, Char.toString a) :: (make_input S (i+1))

fun make_output [] = []
  | make_output (PROD (X, i, j) :: L) = X :: (make_output L)

fun produces g s = 
    let 
	val db = valOf (B.new prog)
	val n = String.size s
	val succ = make_succ n
	val input = make_input (String.explode s) 1
	val rules = map parse_rule g
	val _ = B.add db (rules @ input @ succ)
	val _ = B.saturate db
	val result = B.query db (PROD("~1", 1, n))
    in
	make_output result
    end

fun can_produce g nt s = Utility.member nt (produces g s)

end

val parens = [
    Cyk.UN("LPAREN", #"("),
    Cyk.UN("RPAREN", #")"),
    Cyk.BIN("S", "LPAREN", "RPAREN"),
    Cyk.BIN("S", "LPAREN", "S'"),
    Cyk.BIN("S", "S", "S"),
    Cyk.BIN("S'", "S", "RPAREN")
];

val legal = Cyk.can_produce parens "S"

fun make_input n =
    let
	val R = Random.rand (67, n)
	val max = ref 0
	fun make_input' remaining opened = 
	    ((
	     if opened > (!max)
	     then max := opened
	     else ()
	    );
	    if remaining = 0 
	    then ""
	    else if opened >= remaining
	    then ")" ^ (make_input' (remaining - 1) (opened - 1))
	    else 
		let
		    val r = Random.randInt R
		in
		    if opened = 0 orelse r > 0
		    then "(" ^ (make_input' (remaining - 1) (opened + 1))
		    else ")" ^ (make_input' (remaining - 1) (opened - 1))
		end)
	val n' = if n mod 2 = 1 then n + 1 else n
	val out = make_input' n' 0
	val _ = TextIO.output(TextIO.stdErr, (Int.toString (!max)))
    in
	out
    end;

(*val SIZE = 200*)

legal (make_input SIZE)

