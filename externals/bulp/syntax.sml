signature SYNTAX = 
sig
    datatype term = ICONST of int 
		  | SCONST of string
		  | VAR of string
		  | F of string * term list
    datatype pred = P of string * term list
		  | N of string * term list 
		  | EQ of term * term 
		  | NEQ of term * term
    type rule = pred * pred list
    type prog = rule list

    val print_term : term -> string
    val print_pred : pred -> string
    val print_rule : rule -> string
    val print : prog -> string
    val vars : term -> term list
    val vars_t : term list -> term list
    val vars_p : pred list -> term list (*Unique list of variables occuring in a list of predicates*)
    val ground : term -> bool
    val fact : pred -> bool
    val has_pred : string -> prog -> bool (*true if program contains positive premise with given name*)
    val has_n_pred : string -> prog -> bool (*true if program contains negative premise with given name*)
end

structure Syntax :> SYNTAX =
struct
    datatype term = ICONST of int 
		  | SCONST of string
		  | VAR of string
		  | F of string * term list
    datatype pred = P of string * term list
		  | N of string * term list 
		  | EQ of term * term 
		  | NEQ of term * term
    type rule = pred * pred list
    type prog = rule list

    fun print_term (ICONST i) = Int.toString i
      | print_term (SCONST s) = s
      | print_term (VAR x) = x
      | print_term (F (n, T)) = n ^ "(" ^ (String.concatWith ", " (map print_term T)) ^ ")"
			       
    fun print_pred (EQ (t1, t2)) = (print_term t1) ^ " = " ^ (print_term t2)
      | print_pred (NEQ (t1, t2)) = (print_term t1) ^ " != " ^ (print_term t2)
      | print_pred (P (n, T)) = n ^ "(" ^ (String.concatWith ", " (map print_term T)) ^ ")"
      | print_pred (N (n, T)) = "-" ^ n ^ "(" ^ (String.concatWith ", " (map print_term T)) ^ ")"

    fun print_rule (C,A) = (String.concatWith " ^ " (map print_pred A)) ^ " -> " ^ (print_pred C)

    fun print R = (String.concatWith "\n" (map print_rule R))


  fun vars (VAR x) = [VAR x]
    | vars (F (_,T)) = Utility.unique (foldl op@ [] (map vars T))
    | vars _ = []

  fun vars_t T = Utility.unique (foldl op@ [] (map vars T))

  (*List of all variables occuring in a predicate*)
  fun vars' (EQ (t1, t2)) = (vars t1) @ (vars t2)
    | vars' (NEQ (t1, t2)) = (vars t1) @ (vars t2)
    | vars' (P (_, T)) = foldl op@ [] (map vars T)
    | vars' (N (_, T)) = foldl op@ [] (map vars T)

  (*Unique list of all variables occuring in a list of predicates*)
  fun vars_p PL = Utility.unique (foldl op@ [] (map vars' PL))

  fun ground (VAR _) = false
    | ground (F (n,T)) = foldl (fn (a,b) => a andalso b) true (map ground T)
    | ground _ = true

  fun fact (P (n,T)) = foldl (fn (a,b) => a andalso b) true (map ground T)
    | fact _ = false

  fun is_pred s (P (name,_)) = s = name
    | is_pred _ _ = false

  fun has_pred' s (_,p) = foldl (fn (a,b) => a orelse b) false (map (is_pred s) p)

  fun has_pred s R = foldl (fn (a,b) => a orelse b) false (map (has_pred' s) R)

  fun is_n_pred s (N (name,_)) = s = name
    | is_n_pred _ _ = false

  fun has_n_pred' s (_,p) = is_n_pred s (hd p)

  fun has_n_pred s R = foldl (fn (a,b) => a orelse b) false (map (has_n_pred' s) R)
end
