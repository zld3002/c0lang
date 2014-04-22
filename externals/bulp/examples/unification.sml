CM.make "../sources.cm";

datatype term = 
	 F of string * termlist
       | VAR of string
     and termlist =
	 NIL
       | CONS of term * termlist

datatype error = CLASH
	       | ARITY
	       | OCCURS

datatype predicate = UNIFY of term * term
		   | UNIFY_LIST of termlist * termlist
		   | NOTIN of term * term
		   | NOTINLIST of term * termlist
		   | ERROR of error
		   | EQ of term * term

structure Predicate : PREDICATE =
struct

structure S = Syntax
structure Eval = McAllester

type predicate = predicate

fun inj_t (VAR s) = S.SCONST s
  | inj_t (F (s, tl)) = S.F ("f", [S.SCONST s, inj_tl tl])
and inj_tl NIL = S.ICONST 0
  | inj_tl (CONS (t, tl)) = S.F ("cons", [inj_t t, inj_tl tl])

fun prj_t (S.SCONST s) = VAR s
  | prj_t (S.F ("f", [S.SCONST s, tl])) = F(s, prj_tl tl)
and prj_tl (S.ICONST 0) = NIL
  | prj_tl (S.F("cons", [t, tl])) = CONS (prj_t t, prj_tl tl)

fun inj_e CLASH = S.SCONST "clash"
  | inj_e ARITY = S.SCONST "arity"
  | inj_e OCCURS = S.SCONST "occurs"

fun prj_e "clash" = CLASH
  | prj_e "arity" = ARITY
  | prj_e "occurs" = OCCURS

fun inj (UNIFY (t1,t2)) = S.P("unify", [inj_t t1, inj_t t2])
  | inj (UNIFY_LIST (tl1, tl2)) = S.P("unify_list", [inj_tl tl1, inj_tl tl2])
  | inj (NOTIN (t1,t2)) = S.P("notin", [inj_t t1, inj_t t2])
  | inj (NOTINLIST (t, tl)) = S.P("notinlist", [inj_t t, inj_tl tl])
  | inj (ERROR e) = S.P("error", [inj_e e])
  | inj (EQ (t1, t2)) = S.EQ(inj_t t1, inj_t t2)

fun prj (S.P("unify", [t1, t2])) = UNIFY(prj_t t1, prj_t t2)
  | prj (S.P("unify_list", [tl1, tl2])) = UNIFY_LIST(prj_tl tl1, prj_tl tl2)
  | prj (S.P("notin", [t1, t2])) = NOTIN(prj_t t1, prj_t t2)
  | prj (S.P("notinlist", [t, tl])) = NOTINLIST(prj_t t, prj_tl tl)
  | prj (S.P("error", [S.SCONST e])) = ERROR (prj_e e)
  | prj (S.EQ (t1,t2)) = EQ (prj_t t1, prj_t t2)
end

structure B = Bulp(Predicate)
