signature CHECK = 
sig
    (*Well-formedness checks return NONE on success or descriptive error message on failure*)

    val positive : Syntax.prog -> string option
    val range : Syntax.prog -> string option
    (*on success also returns computed arities*)
    val arity : Syntax.prog -> (string option * (string, int) HashTable.hash_table option) 
    (*on success also returns the strata if necessary, so (NONE,NONE) means the program is stratified in 1 stratum*)
    val stratification : Syntax.prog -> (string option * Syntax.prog list option) 
    (*All of the above*)
    val all : Syntax.prog -> (string option * (string, int) HashTable.hash_table option * Syntax.prog list option)
end

structure Check :> CHECK = 
struct
open Syntax

fun positive [] = NONE
  | positive ((P _,_)::R) = positive R
  | positive (r::R) = 
    SOME("Syntax error. Conclusions must be positive predicates. (In rule {" ^ 
	 print_rule r ^ "})\n")

exception conflicting_arities of string
fun arity R = 
    let 
	exception NotInTable
	val arities : (string, int) HashTable.hash_table = 
	    HashTable.mkTable (HashString.hashString, op=) (32, NotInTable)
	fun add_pred (P (name, terms)) = 
	    (case HashTable.find arities name of 
		 NONE => HashTable.insert arities (name, List.length terms)
	       | SOME i => 
		 if i = List.length terms 
		 then () 
		 else raise conflicting_arities
				("Predicate \"" ^ name ^ "\" has conflicting arities (" ^
				 Int.toString i ^ ", " ^ Int.toString (List.length terms) ^")\n")
	    )
	  | add_pred (N (name,terms)) = add_pred (P (name,terms))
	  | add_pred _ = ()
	fun add_rule (c, p) = app add_pred p before add_pred c
    in
	app add_rule R; (NONE, SOME (arities)) handle conflicting_arities s => (SOME s, NONE)
    end

(*Restricting premises (positive ones)*)
fun restricting [] = []
  | restricting (P(n,T) :: L) = P(n,T) :: restricting L
  | restricting (_::L) = restricting L

fun range [] = NONE
  | range ((r as (c,p))::R) = 
    let
	val restrict = restricting p
	val non_restrict = Utility.difference p restrict
	val unrestricted = Utility.difference (vars_p (c::non_restrict)) (vars_p restrict)
    in
	if unrestricted = []
	then range R
	else SOME(
	     "Program not range restriced. In rule {" ^
	     print_rule r ^ "}, variable" ^ 
	     (if List.length unrestricted > 1 then "s " else " ") ^
	     (String.concatWith ", " (map print_term unrestricted)) ^
	     (if List.length unrestricted > 1 then " are" else " is") ^
	     " unrestricted.\n")
    end
    
(*Helper functions for stratification*)
exception cyclic of string

fun contains_N [] = 0
  | contains_N (N(_)::L) = 1
  | contains_N (_::L) = contains_N L
			
fun count_negated [] = 0
  | count_negated (r::L) = contains_N r + (count_negated L)

fun has_negated s [] = false
  | has_negated s (N(s',_)::L) = if s = s' then true else has_negated s L
  | has_negated s (_::L) = has_negated s L

fun order_rules (r1 as (P(s1,_),p1)) (r2 as (P(s2,_),p2)) = 
    let
	val has12 = has_negated s2 p1
	val has21 = has_negated s1 p2
    in
	if has12 andalso not has21 then GREATER
	else if has21 andalso not has12 then LESS
	else if not has21 andalso not has12 then EQUAL
	else raise cyclic ("Program is not stratified. Rules {" ^ print_rule r1 ^ "} and {" ^
			   print_rule r2 ^ "} are not stratified.\n")
    end

fun overall_order ord [] = ord
  | overall_order EQUAL (ord::O) = overall_order ord O
  | overall_order ord (EQUAL::O) = overall_order ord O
  | overall_order ord1 (ord2::O) = 
    if ord1 <> ord2 
    then raise cyclic ("Program is not stratified. Violation involves at least 3 rules.\n")
    else overall_order ord1 O

fun stratification [] = (NONE,NONE)
  | stratification [r as (P(s,_),p)] = 
    if has_negated s p 
    then (SOME("Program is not stratified. Rule {" ^ print_rule r ^ "} is not stratified.\n"), NONE)
    else (NONE,NONE)
  | stratification R = 
    let 
	val max_strata = count_negated (map (fn (a,b) => b) R)
	val strata = Array.tabulate (2 * max_strata + 1, fn _ => []:rule list)

	fun detect_cycle r =
	    let 
		val strata' = Array.foldr (fn ([], b) => b | (a,b) => a::b) [] strata
		val orders = map (fn L => overall_order EQUAL (map (order_rules r) L)) strata'
		val orders' = List.filter (fn x => x <> EQUAL) orders
		fun violation [] = false
		  | violation (LESS::GREATER::L) = true (*r is below low stratum but above high stratum*)
		  | violation (_::L) = violation L
	    in
		if violation orders'
		then SOME("Program is not stratified. Negative cycle involves rule {" ^ print_rule r ^ "}.\n")
		else NONE
	    end

	fun insert_new r i = 
	    let 
		fun move fin d i = 
		    if i = fin 
		    then ()
		    else Array.update(strata, i, Array.sub(strata, i+d)) before move fin d (i+d)
		val (d,start) = if i < max_strata then (1,0) else (~1,2*max_strata)				  
	    in 
		move i d start before Array.update(strata,i,[r])
	    end

	fun insert r i = 
	    let 
		val L = Array.sub (strata,i)
		val ord = overall_order EQUAL (map (order_rules r) L)
	    in 
		(case ord of EQUAL => Array.update(strata, i, r::L)
			   | GREATER => 
			     if i >= max_strata 
			     then insert r (i+1) 
			     else insert_new r i (* -> higher stratum than i-1, but lower tha i *)
			   | LESS => 
			     if i <= max_strata 
			     then insert r (i-1) 
			     else insert_new r i (* -> lower stratum than i+1, but higher than i *)
		)
	    end

	fun loop [] = 
	    let 
		val strata_list = Array.foldr (fn ([], L) => L | (L1,L2) => L1::L2) [] strata
	    in
		if List.length strata_list <= 1 
		then (NONE,NONE)
		else (NONE,SOME strata_list)
	    end
	  | loop (r::R) = 
	    (case stratification [r] of 
		 (SOME s, _) => (SOME s, NONE)
	       | (NONE, _) => 
		 (case detect_cycle r of
		      SOME s => (SOME s, NONE)
		    | NONE => (insert r max_strata; loop R)
		 )
	    )
    in
	loop R handle cyclic s => (SOME s, NONE)
    end

    

fun all R = 
    let
	val pos = positive R
	val ran = range R
	val (ari_err, ari) = arity R
	val (str_err, str) = stratification R
	fun get_err [] = NONE
	  | get_err (NONE::L) = get_err L
	  | get_err ((SOME s)::L) = SOME s
	val err = get_err [pos,ran,ari_err,str_err]
    in
	(case err of SOME s => (SOME s, NONE, NONE)
		   | NONE => (NONE, ari, str) )
    end
end
