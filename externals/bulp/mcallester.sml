structure McAllester :> EVALUATOR = 
struct

type pred_data = {
     arity : int,
     actions : Action.action Array.array,
     n_actions : Action.action Array.array,
     (* fact, ancestor numbers, next ancestor number, offspring list (predicate, term, number) *)
     facts : (Term.term_rep list, IntSet.set ref * int ref * (int * Term.term_rep list ref * int) list ref) MyHashTable.hash_table,
     (* Table of facts whose nonexistance was used in some derivation, together with references to the derived facts*)
     negations : (Term.term_rep list, (int * Term.term_rep list ref * int) list ref) MyHashTable.hash_table
}

datatype pred_n = POS of int
		| NEG of int

type fact = {pred : pred_n, args : Term.term_rep list, offspring : (int * Term.term_rep list ref * int) list ref}

(*Bool arrays : which predicates need to be queued in this stratum*)
type queue = {pos : bool Array.array, neg : bool Array.array, facts : fact Queue.queue}

type db = {
     data : pred_data Array.array,
     inj : string -> int option, (*Outer predicate names to inner*)
     prj : int -> string option, (*Inner predicate names to outer*)
     queues : queue Array.array, 
     seed : int -> bool (*Which predicates can be added and deleted through the interface*)
}


(*Debugging functions*)
fun say_fact (db:db) i f = Utility.say ("P(" ^ 
				   (case (#prj db) i of NONE => Int.toString i
						      | SOME s => s) ^
				   " | " ^ Term.print_term_list f ^
				   ")")

fun say_fact' (db:db) i f = Utility.say ("    P(" ^ 
				   (case (#prj db) i of NONE => Int.toString i
						      | SOME s => s) ^
				   " | " ^ Term.print_term_list f ^
				   ")")
(*DB interaction*)
fun enqueue (db:db) pn f off = 
    let
	fun enq i ({pos = A, facts = Q, ...} : queue) = 
	    if Array.sub(A,i) 
	    then Queue.enqueue (Q, {pred = POS i, args = f, offspring = off})
	    else ()
	fun n_enq i ({neg = A, facts = Q, ...} : queue) =
	    if Array.sub(A,i) 
	    then Queue.enqueue (Q, {pred = NEG i, args = f, offspring = off})
	    else ()
    in
	case pn 
	 of POS i => Array.app (enq i) (#queues db)
	  | NEG i => Array.app (n_enq i) (#queues db)
    end

fun rem_fact (db:db) (i, f, n) =
    (case MyHashTable.find (#facts (Array.sub((#data db), i))) (!f) of
	 NONE => ()
       | SOME (I, _, off) => 
	 I := (IntSet.delete (!I, n)) before
	 (if IntSet.isEmpty (!I)
	  then (ignore(MyHashTable.remove (#facts (Array.sub((#data db), i))) (!f));
		enqueue db (NEG i) (!f) (ref []);
		app (rem_fact db) (!off)
		(*; Utility.say ("Removing " ^ Int.toString i ^ " - " ^ Term.print_term_list (!f))*)
	       )
	  else ()
	 )
    )

fun rem_negation (db:db) i f =
    (case MyHashTable.find (#negations (Array.sub((#data db), i))) f of
	 NONE => ()
       | SOME _ =>
	 app (rem_fact db) (!(MyHashTable.remove (#negations (Array.sub((#data db), i))) f))
    )

fun add_fact (db:db) i f OFF = 
    let
	fun add_off i f n off = off := (i, ref f, n)::(!off)
    in
	(case MyHashTable.find (#facts (Array.sub((#data db), i))) f of
	     NONE => 
	     let
		 val noff = ref []
	     in
		 MyHashTable.insert (#facts (Array.sub((#data db), i))) (f, (ref (IntSet.singleton 0), ref 1, noff)) before
		 enqueue db (POS i) f noff before 
		 app (add_off i f 0) OFF before
		 rem_negation db i f
	     end
	   | SOME (anc, nanc, _) => 
	     if (#seed db) i
	     then ()
	     else
		 anc := IntSet.add(!anc, !nanc) before
		 app (add_off i f (!nanc)) OFF before
		 nanc := !nanc + 1
	)
    end

fun add_negation (db:db) i f =
    (case MyHashTable.find (#negations (Array.sub((#data db), i))) f of
	 NONE => 
	 let 
	     val off = ref [] 
	     val _ = MyHashTable.insert (#negations (Array.sub((#data db), i))) (f, off)
	 in
	     off
	 end
       | SOME off => off
    )

fun has_fact (db:db) i f = 
    (case MyHashTable.find (#facts (Array.sub((#data db), i))) f of
	 SOME _ => true
       | NONE => false)

fun find_facts (db:db) i f = 
	map (fn (T, (_, _, off)) => (T,off)) (MyHashTable.find_hashi (#facts (Array.sub((#data db), i))) f) 

type database = db ref

(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 *Saturate
 *)
fun saturate (db':database) = 
    let 
	val db = !db'
	val data = #data db
	fun process_fact ({pred, args, offspring}, i) = 
	    let
		val action = 
		    case pred 
		     of POS j => (Array.sub(#actions (Array.sub(data, j)), i))
		      | NEG j => (Array.sub(#n_actions (Array.sub(data, j)), i))
	    in 
		(action args offspring : unit)
	    end
	fun process_stratum (i,{facts = Q, ...} : queue) = 
	    while not (Queue.isEmpty Q) do
	    process_fact (Queue.dequeue Q, i)
    in
	Array.appi process_stratum (#queues db)
    end

(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 *query
 *)
fun query (db':database) (p as Syntax.P(n,T)) = 
    (case (#inj (! db')) n of 
	 NONE => (Utility.say ("Unknown predicate name :\"" ^ n ^ "\"."); [])
       | SOME i => 
	 let 
	     val db = !db'
	     val (T',nvars) = Rename.rename_term_list T
	     val T'' = map Term.inj T'
	     val ar = #arity (Array.sub(#data db, i))
	     val ar_T = List.length T
	     val facts = MyHashTable.listItemsi (#facts (Array.sub(#data db, i)))
	     fun get_facts [] = []
	       | get_facts ((f,_)::F) = 
		 (case Term.get_subst_list nvars T'' f of
		      NONE => get_facts F
		    | SOME _ => Syntax.P(n, map Term.prj f)::(get_facts F)
		 )
	 in 
	     if ar <> ar_T
	     then (Utility.say ("Wrong arity in predicate [" ^ Syntax.print_pred p ^"] is " ^
			     Int.toString ar_T ^ ", should be " ^ Int.toString ar ^ "."); [])
	     else get_facts facts
	 end
	  )
  | query _ _ = (Utility.say ("Only positive predicates can be queried."); [])

(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 *new
 *)
exception NotInTable

fun new R = 
    let
	val (err, _, _) = Check.all R
    in
	(case err of 
	     SOME s => (Utility.say ("Program error : " ^ s); NONE)
	   | NONE => 
	     let
		 val (R', inj, prj, maxP, seeding) = Transform.transform R
		 val (_, arities) = Check.arity R'
		 val (_, strata') = Check.stratification R'
		 val strata = (case strata' of NONE => [R'] | SOME S => S)
		 fun tabulate arity i : pred_data =
		     {arity = HashTable.lookup arity (Int.toString i),
		      actions = Array.tabulate(List.length strata, fn _ => (fn _ => (fn _ => ()))), (*dummy actions, updated below*)
		      n_actions = Array.tabulate(List.length strata, fn _ => (fn _ => (fn _ => ()))),
		      facts = MyHashTable.mkTable 
				  (fn T => Term.hash (hd T), 
				   fn (T1,T2) => 
				      if List.length T1 = List.length T2 
				      then foldl (fn (a,b) => a andalso b) 
						 true 
						 (map Term.eq (ListPair.zip (T1,T2))) 
				      else false)
				  (500, NotInTable),
		     negations = MyHashTable.mkTable 
				  (fn T => Term.hash (hd T), 
				   fn (T1,T2) => 
				      if List.length T1 = List.length T2 
				      then foldl (fn (a,b) => a andalso b) 
						 true 
						 (map Term.eq (ListPair.zip (T1,T2))) 
				      else false)
				  (500, NotInTable)}

		 fun make_queue S = 
		     {pos = Array.tabulate (maxP, fn p => Syntax.has_pred (Int.toString p) S), 
		      neg = Array.tabulate (maxP, fn p => Syntax.has_n_pred (Int.toString p) S), 
		      facts = Queue.mkQueue() : fact Queue.queue
		     }
		     
		 val db = {
		     data = Array.tabulate (maxP, tabulate (valOf arities)),
		     inj = inj,
		     prj = prj,
		     queues = Array.tabulate(List.length strata, fn i => make_queue (List.nth (strata,i))),
		     seed = fn i => Array.sub(seeding,i)
		 }:db
		 val all_actions = map (Action.get_actions maxP) strata
		 val all_n_actions = map (Action.get_n_actions maxP) strata
		 fun update_action (i,{actions = _, n_actions = _, arity = a, facts = f, negations = n} : pred_data) = {
		     actions = Array.tabulate(List.length strata,
					   fn j => (Array.sub (List.nth (all_actions, j) ,i))
						       (add_fact db) (add_negation db) (has_fact db) (find_facts db)
					     ),
		     n_actions = Array.tabulate(List.length strata,
					     fn j => (Array.sub (List.nth (all_n_actions, j) ,i))
							 (add_fact db) (add_negation db) (has_fact db) (find_facts db)
					       ),
		     arity = a,
		     facts = f,
		     negations = n
		     } : pred_data
		 val _ = Array.modifyi update_action (#data db)
	     in 
		 SOME (ref db)
	     end
	)
    end
    
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 *add
 *)

exception IllegalFact of string

fun add db' pl = 
    let
	val db = !db'
	fun add_pred db (p as Syntax.P(name, T)) = 
	    (case (#inj db) name of 
		 NONE => raise IllegalFact ("Unknown predicate name :\"" ^ name ^ "\".")
	       | SOME i => if not (Syntax.fact p)
			   then raise IllegalFact ("Not a fact: [" ^ Syntax.print_pred p ^"].")
			   else if not ((#seed db) (valOf ((#inj db) name)))
			   then raise IllegalFact ("Not a seeding predicate : " ^ name)
			   else
			       let 
				   val T' = map Term.inj T handle _ => (Utility.say(String.concatWith " " (map Syntax.print_term T));[])
				   val ar = #arity (Array.sub(#data db, i))
				   val ar_T = List.length T
			       in 
				   if ar <> ar_T
				   then raise IllegalFact 
					      ("Wrong arity in fact [" ^ Syntax.print_pred p ^"] is " ^
					       Int.toString ar_T ^ ", should be " ^ Int.toString ar ^ ".")
				   else add_fact db i T' []
			       end
	    )
	  | add_pred db p = raise IllegalFact ("Not a fact: [" ^ Syntax.print_pred p ^"].")
    in
	app (add_pred db) pl
	handle IllegalFact s => Utility.say("Error adding facts. " ^ s ^ " Facts up to here were added.")
	     | NotInTable => Utility.say("NotInTable")
	     | _ => Utility.say("Error adding facts.")
    end

fun rem db' pl =
    let
	val db = !db'
	fun rem_pred (db:db) (p as Syntax.P(name, T)) = 
	    (case (#inj db) name of 
		 NONE => raise IllegalFact ("Unknown predicate name :\"" ^ name ^ "\".")
	       | SOME i => if not (Syntax.fact p)
			   then raise IllegalFact ("Not a fact: [" ^ Syntax.print_pred p ^"].")
			   else if not ((#seed db) (valOf ((#inj db) name)))
			   then raise IllegalFact ("Not a seeding predicate : " ^ name)
			   else
			       let 
				   val T' = map Term.inj T handle _ => (Utility.say(String.concatWith " " (map Syntax.print_term T));[])
				   val ar = #arity (Array.sub(#data db, i))
				   val ar_T = List.length T
			       in 
				   if ar <> ar_T
				   then raise IllegalFact 
					      ("Wrong arity in fact [" ^ Syntax.print_pred p ^"] is " ^
					       Int.toString ar_T ^ ", should be " ^ Int.toString ar ^ ".")
				   else rem_fact db (i, ref T', 0)
			       end
	    )
	  | rem_pred db p = raise IllegalFact ("Not a fact: [" ^ Syntax.print_pred p ^"].")
    in
	app (rem_pred db) pl
	handle IllegalFact s => Utility.say("Error removinging facts. " ^ s ^ " Facts up to here were removed.")
	     | NotInTable => Utility.say("NotInTable")
	     | _ => Utility.say("Error removing facts.")
    end

end (*struct*)
