signature ACTION =
sig
   type action = Term.term_rep list -> (int * Term.term_rep list ref * int) list ref -> unit
   type abstract_action = (int -> Term.term_rep list -> (int * Term.term_rep list ref * int) list ref list -> unit) (*Add facts*)
			  -> (int -> Term.term_rep list -> (int * Term.term_rep list ref * int) list ref) (*Add negations*)
			  -> (int -> Term.term_rep list -> bool) (*Test for existence of a fact*)
			  (*Get all facts that have the same first term*)
			  -> (int -> Term.term_rep list -> (Term.term_rep list * (int * Term.term_rep list ref * int) list ref) list) 
			  -> action
   val get_actions : int -> Syntax.prog -> abstract_action Array.array 
   val get_n_actions : int -> Syntax.prog -> abstract_action Array.array
end

structure Action :> ACTION=
struct

datatype pred = P of int * Term.term_rep list
	      | N of int * Term.term_rep list 
	      | EQ of Term.term_rep * Term.term_rep 
	      | NEQ of Term.term_rep * Term.term_rep
	      | NOP

type rule = int * pred * pred list

type action = Term.term_rep list -> (int * Term.term_rep list ref * int) list ref -> unit
type abstract_action = (int -> Term.term_rep list -> (int * Term.term_rep list ref * int) list ref list -> unit) (*Add facts*)
		       -> (int -> Term.term_rep list -> (int * Term.term_rep list ref * int) list ref) (*Add negations*)
		       -> (int -> Term.term_rep list -> bool) (*Test for existence of a fact*)
		       (*Get all facts that have the same first term*)
		       -> (int -> Term.term_rep list -> (Term.term_rep list * (int * Term.term_rep list ref * int) list ref) list) 
		       -> action

fun inj_pred (Syntax.P (s,TL)) = P(valOf (Int.fromString s), map Term.inj TL)
  | inj_pred (Syntax.N (s,TL)) = N(valOf (Int.fromString s), map Term.inj TL)
  | inj_pred (Syntax.EQ (t1,t2)) = EQ(Term.inj t1, Term.inj t2)
  | inj_pred (Syntax.NEQ (t1,t2)) = NEQ(Term.inj t1, Term.inj t2)

fun prj_pred (P (i, TL)) = Syntax.P (Int.toString i, map Term.prj TL)
  | prj_pred (N (i, TL)) = Syntax.N (Int.toString i, map Term.prj TL)
  | prj_pred (EQ (t1,t2)) = Syntax.EQ (Term.prj t1, Term.prj t2)
  | prj_pred (NEQ (t1,t2)) = Syntax.NEQ (Term.prj t1, Term.prj t2)

fun inj_rule ((c,p),i) = (i, inj_pred c, map inj_pred p)

fun tl_eq [] [] = true
  | tl_eq (t1::T1) (t2::T2) = Term.eq (t1,t2) andalso tl_eq T1 T2
  | tl_eq _ _ = false

fun pred_eq (P (n1,T1)) (P (n2,T2)) = n1 = n2 andalso tl_eq T1 T2
  | pred_eq (N (n1,T1)) (N (n2,T2)) = n1 = n2 andalso tl_eq T1 T2
  | pred_eq (EQ (t11,t12)) (EQ (t21,t22)) = Term.eq (t11,t21) andalso Term.eq (t12,t22)
  | pred_eq (NEQ (t11,t12)) (NEQ (t21,t22)) = Term.eq (t11,t21) andalso Term.eq (t12,t22)
  | pred_eq _ _ = false

fun compress R = 
    let
	fun eq_rel ( (i1,c1,p1) : rule, (i2,c2,p2) : rule ) = pred_eq (hd p1) (hd p2)
	val Eq = Utility.eq_classes eq_rel R
	fun comp (Eq:rule list) = 
	    let
		val min = Utility.min (map #1 Eq)
		val p1 = hd (#3 (hd Eq))
		fun rest (i,c,p) = (i,c, (case tl p of [] => NOP | [p'] => p'))
	    in
		(min, p1, map rest Eq)
	    end
	    
    in
	map comp Eq
    end

fun make_n_action R pred_num add add_n exists find : action =
    let
	val cases = compress R
	fun apply sub T (i, P(cname, CT), P(name2, T2)) =
	    let
		val CT' = Term.apply_subst_list sub CT
		val T2' = Term.apply_subst_list sub T2
		val Ts = find name2 T2'
		val subs = map (fn (TS, offs) => (Term.get_subst_list i T2' TS, offs)) Ts
	    in
		app (fn (NONE, _) => ()
		      | (SOME sub', offs) => 
			let
			    val off = add_n pred_num T
			in
			    add cname (Term.apply_subst_list sub' CT') [off, offs]
			end
		    )
		    subs
	    end
	fun act T (i, N(name, PT), L) =
	    let
		val subst = Term.get_subst_list i PT T
	    in 
		(case subst of
		     NONE => ()
		   | SOME sub => app (apply sub T) L
		)
	    end
    in
	if List.null cases
	then fn _ => (fn _ => ())
	else fn T => (fn _ => 
			 if exists pred_num T
			 then ()
			 else app (act T) cases)
    end

fun make_action R add add_n exists find : action = 
    let
	val cases = compress R
	fun apply sub off (i, P(name,T), p2) =
	    (case p2 of 
		 NOP => add name (Term.apply_subst_list sub T) [off]
	       | EQ(t1,t2) => if Term.eq (Term.apply_subst sub t1, Term.apply_subst sub t2)
			      then add name (Term.apply_subst_list sub T) [off]
			      else ()
	       | NEQ(t1,t2) => if not (Term.eq (Term.apply_subst sub t1, Term.apply_subst sub t2))
			       then add name (Term.apply_subst_list sub T) [off]
			       else ()
	       | N(name2,T2) => if exists name2 (Term.apply_subst_list sub T2)
				then ()
				else 
				    let
					val off' = add_n name2 T2
				    in 
					add name (Term.apply_subst_list sub T) [off, off']
				    end
	       | P(name2,T2) => 
		 let 
		     val T' = Term.apply_subst_list sub T
		     val T2' = Term.apply_subst_list sub T2
		     val Ts = find name2 T2'
		     val subs = map (fn (TS, offs) => (Term.get_subst_list i T2' TS, offs)) Ts
		 in
		     app (fn (NONE, _) => ()
			   | (SOME sub', offs) => 
			     add name (Term.apply_subst_list sub' T') [off, offs])
			 subs
		 end
	    )
	    
	fun act T off (i, P(name, PT), L) = 
	    let
		val subst = Term.get_subst_list i PT T
	    in 
		(case subst of
		     NONE => ()
		   | SOME sub => app (apply sub off) L
		)
	    end
    in
	if List.null cases
	then fn _ => (fn _ => ())
	else fn T => (fn off => app (act T off) cases)
    end

fun filter_rule i (r as ((c,[]))) = []
  | filter_rule i (r as (c,[Syntax.P(name,T)])) = if Int.toString i = name then [r] else []
  | filter_rule i (r as (c,[Syntax.P(name,T),a2])) = 
    (if Int.toString i = name then [r] else []) @
    (case a2 of 
	 Syntax.P(name2, T2) => if Int.toString i = name2 then [(c,[a2,Syntax.P(name,T)])] else []
       | _ => []
    )
  | filter_rule _ _ = []

fun filter_n_rule i (r as (c,[Syntax.N(name,T),a2])) = if Int.toString i = name then [r] else []
  | filter_n_rule _ _ = []

fun get_rules i R = map (inj_rule o Rename.rename_rule) (foldl op@ [] (map (filter_rule i) R))

fun get_n_rules i R = map (inj_rule o Rename.rename_rule) (foldl op@ [] (map (filter_n_rule i) R))

fun get_actions n R = Array.tabulate(n, fn i => make_action (get_rules i R))

fun get_n_actions n R = Array.tabulate(n, fn i => make_n_action (get_n_rules i R) i)
end
