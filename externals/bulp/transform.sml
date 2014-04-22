signature TRANSFORM = 
sig
    val transform : 
	Syntax.prog -> (Syntax.prog * (*Transformed program*)
			(string -> int option) * (*Predicate names to internal number*)
			(int -> string option) * (*Internal number to predicate names*)
			int * (*Highest predicate number used*)
			bool Array.array) (*Which predicates are seeding*)
end

structure Transform :> TRANSFORM =
struct
open Syntax

(*supply of fresh predicates*)
local
    val pred_counter = ref 0
    val func_counter = ref 0
    (* It seems reasonable to assume that no user will ever 
     * name a function "gqgkwx[0-9]*". Complete safety is hard
     * to achieve since new function names may be introduced
     * with every fact added to the database
     *)
    val func_prefix = "gqgkwx"  
in
fun freshp () = Int.toString (!pred_counter) before (pred_counter := !pred_counter + 1)
fun freshf () = func_prefix ^ Int.toString (!func_counter) before (func_counter := !func_counter + 1)
fun reset () = pred_counter := 0 before func_counter := 0
fun getp () = !pred_counter
end

fun rename_name (inj:(string,int) HashTable.hash_table) prj name = 
    (case HashTable.find inj name of 
	 SOME p => Int.toString p
       | NONE => 
	 let 
	     val p = freshp()
	 in
	     (HashTable.insert inj (name, valOf (Int.fromString p));
	      prj := !prj @ [name];
	      p)
	 end
    )
    

fun rename_pred inj prj (P(n,T)) = P(rename_name inj prj n, T)
  | rename_pred inj prj (N(n,T)) = N(rename_name inj prj n, T)
  | rename_pred inj prj e = e

fun rename_rule inj prj ((c,p):rule) = (rename_pred inj prj c, map (rename_pred inj prj) p)

fun rename inj prj ([]:prog) = []
  | rename inj prj (r::R) = (rename_rule inj prj r) :: (rename inj prj R)

(*Ensure range restriction is preserved by binarization*)
fun prep_rule ((c,p):rule) = 
    let 
	fun greater (P(name1,_),P(name2,_)) = name1 < name2
	  | greater (_,P(_,_)) = true
	  | greater _ = false
    in
	(c,ListMergeSort.sort greater p)
    end

fun binarize_rule ((c,[]):rule) = [(c,[])]
  | binarize_rule (c,[a]) = [(c,[a])]
  | binarize_rule (c,[a1,a2]) = [(c,[a1,a2])]
  | binarize_rule (c,a1::a2::A) = 
    let
	val p = P(freshp (), Utility.intersection (vars_p [a1,a2]) (vars_p (c::A)))
    in
	(p, [a1,a2]) :: (binarize_rule (c, p::A))
    end

fun binarize R = foldl op@ [] (map (binarize_rule o prep_rule) R)

(* Check whether indexing is necessary *)

fun index_nec T1 T2 = 
    let
	val v1 = vars_t T1
	val v2 = vars_t T2
	val isec = Utility.intersection v1 v2
	val h1 = List.filter (fn t => Utility.eq (vars t) isec) T1
	val h2 = List.filter (fn t => Utility.eq (vars t) isec) T2
    in
	if List.length h1 = 1 andalso List.length h2 = 1
	then 
	    let
		val T1' = h1 @ (Utility.difference T1 h1)
		val T2' = h2 @ (Utility.difference T2 h2)
	    in
		SOME (if T1 = T1' then NONE else SOME T1', if T2 = T2' then NONE else SOME T2')
	    end
	else NONE
    end

fun index_nec_n T1 T2 = 
    let
	val v1 = vars_t T1
	val v2 = vars_t T2
	val isec = Utility.intersection v1 v2
	val h2 = List.filter (fn t => Utility.eq (vars t) isec) T2
    in
	if List.length h2 = 1
	then 
	    let
		val T2' = h2 @ (Utility.difference T2 h2)
	    in
		SOME (NONE, if T2 = T2' then NONE else SOME T2')
	    end
	else NONE
    end

fun index_n (r as (c, [N(n1, T1), P(n2, T2)])) = 
    (case index_nec_n T1 T2 
      of SOME (_, NONE) => 
	 [r]
       | SOME (_, SOME T2') =>
	 let
	     val p2 = freshp()
	 in
	     [(P(p2,T2'),[P(n2,T2)]), (c, [N(n1, T1), P(p2,T2')])]
	 end
       | NONE =>
	 let
	     val p2 = freshp()
	     val v1 = vars_t T1
	     val v2 = vars_t T2
	     val f = F(freshf (), Utility.difference v2 v1)
	     val g = F(freshf (), v1)
	 in
	     [(P(p2, [g, f]), [P(n2, T2)]), (c, [N(n1, T1), P(p2, [g, f])])]
	 end)

fun index_rule ((c,[]):rule) = [(c,[])]
  | index_rule (c,[a]) = [(c,[a])]
  | index_rule (r as (c,[a1,a2])) = 
    (case (a1,a2) of 
	 (P (n1,T1), P (n2,T2)) => 
	 (case index_nec T1 T2 of 
	      SOME T' =>
	      (case T' of 
		   (NONE, NONE) => 
		   [(c,[P(n1,T1),P(n2,T2)])]
		 | (NONE, SOME T2') =>
		   let
		       val p2 = freshp()
		   in
		       [(c,[P(n1,T1),P(p2,T2')]), (P(p2,T2'),[P(n2,T2)])]
		   end
		 | (SOME T1', NONE) => 
		   let 
		       val p1 = freshp()
		   in
		       [(c,[P(p1,T1'),P(n2,T2)]), (P(p1,T1'),[P(n1,T1)])]
		   end
		 | (SOME T1', SOME T2') =>
		   let 
		       val p1 = freshp()
		       val p2 = freshp()
		   in
		       [(c,[P(p1,T1'),P(p2,T2')]), (P(p1,T1'),[P(n1,T1)]), (P(p2,T2'),[P(n2,T2)])]
		   end
		   
		   
	      )
	    | NONE =>
	      let
		  val v1 = vars_p [a1]
		  val v2 = vars_p [a2]
		  val f = F(freshf (), Utility.difference v1 v2)
		  val g = F(freshf (), Utility.intersection v1 v2)
		  val h = F(freshf (), Utility.difference v2 v1)
		  val p1 = freshp ()
		  val p2 = freshp ()
		  val q = freshp ()
	      in 
		  [
		   (P(p1, [g,f]), [a1]),
		   (P(p2, [g,h]), [a2]),
		   (P(q, [VAR("x"),VAR("y"),VAR("z")]), 
		    [
		     P(p1, [VAR("y"), VAR("x")]),
		     P(p2, [VAR("y"), VAR("z")])
		   ]),
		   (c, [P(q, [f,g,h])])
		  ]
	      end
	 )
       | (P _, N _) => [(c,[a1,a2])] @ (index_n (c,[a2,a1]))
       | (N _, P _) => [(c,[a2,a1])] @ (index_n r)
       | (P _, _) => [(c,[a1,a2])]
       | (_, P _) => [(c,[a2,a1])]
    )

fun index R = foldl op@ [] (map index_rule R)

fun seeding n R =
    let
	val conclusions = map (fn (P(s,_),_) => s) R
	fun is_conclusion s = Utility.member s conclusions
    in
	Array.tabulate(n, fn i => not(is_conclusion (Int.toString i)))
    end

fun transform R = 
    let
	exception UnknownName
	val inj' = HashTable.mkTable (HashString.hashString, op=) (32, UnknownName)
	val prj'' = ref []
	val _ = reset()
	val R' = rename inj' prj'' R
	val prj' = Array.tabulate(getp(), fn i => List.nth (!prj'', i))
	val inj = fn s => HashTable.find inj' s
	val prj = fn i => SOME (Array.sub (prj', i)) handle Subscript => NONE
	val R'' = index (binarize R')
    in
	(R'', inj, prj, getp(), seeding (getp()) R'')
    end
end
