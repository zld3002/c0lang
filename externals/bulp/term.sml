(*Internal hash-consed representation of terms*)
signature TERM = 
sig
    type term_rep
    val inj : Syntax.term -> term_rep
    val prj : term_rep -> Syntax.term
    val eq : term_rep * term_rep -> bool (*constant time equality*)
    val hash : term_rep -> word (*constant time hash*)

    type subst (*substitution*)

    (* substitiution that transforms first term into second term, if one exists,
     * integer indicates number of variables in first term
     *)
    val get_subst : int -> term_rep -> term_rep -> subst option

    val apply_subst : subst -> term_rep -> term_rep 
    val get_subst_list : int -> term_rep list -> term_rep list -> subst option
    val apply_subst_list : subst -> term_rep list -> term_rep list

    (*printing*)
    val print_term : term_rep -> string
    val print_term_list : term_rep list -> string
end

structure Term :> TERM =
struct 
  
  (*Hash cons representation*)
  structure HashConsInt = HashConsGroundFn (
    struct
      type hash_key = int
      val sameKey = (op= : int * int -> bool)
      val hashVal = fn k => Word.fromInt(((k mod 29611) * 4730) mod 29611)
    end)

  datatype 'a hc_list_node
    = HC_NIL
    | HC_CONS of 'a * 'a hc_list
  withtype 'a hc_list = 'a hc_list_node HashCons.obj

  type const = HashConsInt.obj
  type name = HashConsString.obj
  datatype term_node
    = ICONST of const
    | SCONST of name
    | VAR of const (*Variables are integers too*)
    | FUN of name * term hc_list
  withtype term = term_node HashCons.obj

  fun hc_listeq (HC_NIL, HC_NIL) = true
    | hc_listeq (HC_CONS (e1, L1), HC_CONS (e2, L2)) = HashCons.same(e1,e2) andalso HashCons.same(L1,L2)
    | hc_listeq _ = false

  fun eq (ICONST c1, ICONST c2) = HashCons.same(c1,c2)
    | eq (SCONST s1, SCONST s2) = HashCons.same(s1,s2)
    | eq (VAR n1, VAR n2) = HashCons.same(n1,n2)
    | eq (FUN (n1, F1), FUN (n2, F2)) = HashCons.same(n1,n2) andalso HashCons.same(F1, F2)
    | eq _ = false

  val hc_listtbl = HashCons.new {eq=hc_listeq : term hc_list_node * term hc_list_node -> bool}
  val tbl = HashCons.new {eq=eq}

  val mkNIL = HashCons.cons0 hc_listtbl (0wx1, HC_NIL)
  val mkCONS = HashCons.cons2 hc_listtbl (0wx3, HC_CONS)

  val mkICONST = HashCons.cons1 tbl (0wx5, ICONST)
  val mkSCONST = HashCons.cons1 tbl (0wx7, SCONST)
  val mkVAR = HashCons.cons1 tbl (0wx11, VAR)
  val mkFUN = HashCons.cons2 tbl (0wx13, FUN)
  val const = HashConsInt.mk
  val name = HashConsString.mk

  (*interface*)
  type term_rep = term

  fun inj (Syntax.ICONST c) = mkICONST (const c) 
    | inj (Syntax.SCONST s) = mkSCONST (name s)
    | inj (Syntax.VAR n) = mkVAR (const (valOf (Int.fromString n)))
    | inj (Syntax.F (n, T)) = mkFUN(name n, inj_list T)
  and inj_list [] = mkNIL
    | inj_list (t::T) = mkCONS(inj t, inj_list T)

  fun prj ({nd = FUN (n, L), ...}:term_node HashCons.obj) = Syntax.F(prj_name n, prj_list L)
    | prj {nd = VAR n, ...} = Syntax.VAR(Int.toString (prj_const n))
    | prj {nd = ICONST n, ...} = Syntax.ICONST(prj_const n)
    | prj {nd = SCONST n, ...} = Syntax.SCONST(prj_name n)
  and prj_list {nd = HC_CONS (e, L) , ...} = (prj e)::(prj_list L)
    | prj_list {nd = HC_NIL, ...} = []
  and prj_name {nd = n, ...} = n
  and prj_const {nd = c, ...} = c

  val eq = HashCons.same

  val hash = HashCons.tag

  fun print_term t = Syntax.print_term (prj t)

  fun print_term_list tl = String.concatWith ", " (map (Syntax.print_term o prj) tl)

  (*substitutions*)

  type subst = term option Array.array

  exception NoMatch
  exception NotFound

  fun subst_list (sub:subst) ({nd = HC_NIL, ...}: term hc_list) ({nd = HC_NIL, ...}: term hc_list) = ()
    | subst_list sub {nd = HC_CONS (e1,L1) , ...} {nd = HC_CONS (e2,L2) , ...} = 
      subst sub (e1, e2) before subst_list sub L1 L2
    | subst_list _ _ _ = raise NoMatch
  and subst (sub:subst) ({nd = FUN (n1,L1), ...}:term, {nd = FUN (n2,L2), ...}:term) = 
      if HashCons.same(n1, n2)
      then subst_list sub L1 L2 
      else raise NoMatch
    | subst sub ({nd = VAR n, ...}, t) = Array.update(sub, prj_const n, SOME t)
    | subst sub ({nd = ICONST n1, ...}, {nd = ICONST n2, ...}) = 
      if HashCons.same (n1, n2) 
      then () 
      else raise NoMatch
    | subst sub ({nd = SCONST n1, ...}, {nd = SCONST n2, ...}) = 
      if HashCons.same (n1, n2) 
      then () 
      else raise NoMatch
    | subst _ _ = raise NoMatch

  fun get_subst i t1 t2 =
      let
	  val sub = Array.tabulate(i, fn _ => NONE)
      in
	  subst sub (t1, t2); 
	  SOME sub
	  handle NoMatch => NONE
      end

  fun get_subst_list i T1 T2 = 
      let
	  val sub = Array.tabulate(i, fn _ => NONE)
      in
	  if List.length T1 <> List.length T2
	  then NONE
	  else 
	      (app (subst sub) (ListPair.zip (T1, T2));
	       SOME sub)
	      handle NoMatch => NONE
      end

  fun apply_list sub ({nd = HC_NIL, ...} : term hc_list) = mkNIL
    | apply_list sub {nd = HC_CONS (e, L), ...} = mkCONS(apply sub e, apply_list sub L)
  and apply sub {nd = FUN (n,L), ...} = mkFUN(n, apply_list sub L)
    | apply sub {nd = VAR {nd = n, ...}, ...} = 
      if n < Array.length sub
      then 
	  (case Array.sub (sub,n) of
	       NONE => mkVAR (const n)
	     | SOME t => t
	  )
      else mkVAR (const n)
    | apply sub c = c

  fun apply_subst sub t = apply sub t
      
  fun apply_subst_list sub T = map (apply_subst sub) T

end

