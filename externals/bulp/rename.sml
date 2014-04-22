signature RENAME = 
sig
    val rename_term_list : Syntax.term list -> (Syntax.term list * int)
    val rename_rule : Syntax.rule -> (Syntax.rule * int)
end

structure Rename :> RENAME = 
struct
open Syntax

fun rename_term_listi T inj = 
    let 
	fun rename_vars (F (name, TL)) = F(name, map rename_vars TL)
	  | rename_vars (VAR name) = VAR (inj name)
	  | rename_vars c = c
    in	   
	map rename_vars T
    end

fun rename_term_list T = 
    let
	exception UnknownName
	val i = ref 0
	val inj' = HashTable.mkTable (HashString.hashString, op=) (32, UnknownName)
	fun inj s = (case HashTable.find inj' s of 
			 SOME n => n
		       | NONE => 
			 let
			     val n = Int.toString (!i)
			     val _ = i := (!i + 1)
			     val _ = HashTable.insert inj' (s, n)
			 in
			     n
			 end
		    )
    in 
	(rename_term_listi T inj, !i)
    end

fun rename_rule (c,p) = 
    let
	val i = ref 0
	exception UnknownName
	val inj' = HashTable.mkTable (HashString.hashString, op=) (32, UnknownName)
	fun inj s = (case HashTable.find inj' s of 
			 SOME n => n
		       | NONE => 
			 let
			     val n = Int.toString (!i)
			     val _ = i := (!i + 1)
			     val _ = HashTable.insert inj' (s, n)
			 in
			     n
			 end
		    )
	fun rename_pred (EQ (t1,t2)) = 
	    let 
		val [t1',t2'] = rename_term_listi [t1,t2] inj
	    in
		EQ(t1',t2')
	    end
	  | rename_pred (NEQ (t1,t2)) = 
	    let 
		val [t1',t2'] = rename_term_listi [t1,t2] inj
	    in
		NEQ(t1',t2')
	    end
	  | rename_pred (N (name, T)) = N(name, rename_term_listi T inj)
	  | rename_pred (P (name, T)) = P(name, rename_term_listi T inj)
	val p' = map rename_pred p (*rename premises before conclusion to optimize actinos*)
    in
	((rename_pred c, p'), !i)
    end
end
