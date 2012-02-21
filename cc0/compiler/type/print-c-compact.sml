(* C0 Compiler
 * Printing to C
 * Author: Frank Pfenning <fp@cs.cmu.edu>
 *
 *)

signature PRINT =
sig
    val pp_program : Ast.program -> string
end

(* There are a number of semantic differences that require some care
 * when printing to C.  Some of these are smoothed out by appropriate
 * macros in the various runtimes (c0rt [default], bare [without gc],
 * unsafe [without null-ptr or array bounds checks]).  Others are
 * dealt with here.  We also make certain assumptions about the
 * compilation model used by the specific gcc backend we use.
 *
 * Assumptions:
 * - int has 32 bits.  This file should probably print 'int' as 'int32'.
 * - int used two's complement arithmetic for +, -, *.  This is
 *   achieved by passing -fwrapv to gcc.  An alternative using
 *   unsigned int's in C is awkward (see some comments below).
 * - we assume right shift e1 >> e2 is arithmetical on negative e1.
 *
 * Working around undefined behavior:
 * - null ptr deref is handled by macro cc0_deref(tp, e)
 * - array bounds checking is handled by macro cc0_array_sub(tp, e1, e2)
 *   both of these also work as lvalues for assignments
 * - allocation is handled by macro cc0_alloc(tp)
 * - array allocation is handled by macro cc0_alloc_array(tp, e)
 *   allocations raise an exception if they fail, rather than returning NULL
 *   they also initialize to 0
 * - assertions are handled with macro cc0_assert(e, msg1, msg2, ...)
 * - e1/e2 is compiled as _idiv(e1,e2) to check for overflow
 * - e1%e2 is compiled as _imod(e1,e2) to check for overflow
 * - e1<<e2 is compiled as _sal(e1,e2) to mask e2 to 32 bits
 * - e1>>e2 is compiled as _sar(e1,e2) to mask e2 to 32 bits
 * - evaluation order is undefined, which is handled by isolating
 *   expressions which may have an effect.  For example,
 *   f(g(x),h(3)) might be translated as
 *   int tmp1 = g(x);
 *   int tmp2 = h(3);
 *   int tmp3 = f(tmp1,tmp2);
 *   and then using "tmp3" where the above expression was embedded.
 *   This is explained further in the iso_<cat> functions below.
 *)

structure PrintC =
struct

   structure A = Ast

   (* extend_env env ds = env', extending env with declarations in ds
    * we assume there is no shadowing or name clashes *)
   fun extend_env env (A.VarDecl(id, tp, _, ext)::ds) =
         extend_env (Symbol.bind env (id, tp)) ds
     | extend_env env nil = env

   (* new statement "tp _tmp_<n> = e;" *)
   fun new_tmp_init (tp, e) =
       let val (d, t) = Syn.new_tmp_init (tp, e)
       in (A.StmDecl(d), t) end

   val MINUSONE = Word32.fromInt(~1);
   val THIRTYTWO = Word32.fromInt(32);

   (* is_safe_div p = true if n / p and n % p are known to be defined, for all n.
    * We assume p is a pure expression, without marks. *)
   fun is_safe_div (A.IntConst(w)) =
       w <> Word32Signed.ZERO andalso w <> MINUSONE
     | is_safe_div _ = false

   (* is_safe_shift k = true if 0 <= k & k < 32, so n << k and n >> k is defined.
    * assumes n >> k for negative n is arithmetic right shift, not logical *)
   fun is_safe_shift (A.IntConst(w)) =
       Word32Signed.signed_less(MINUSONE, w)
       andalso Word32Signed.signed_less(w, THIRTYTWO)
     | is_safe_shift _ = false

   (* iso_exp env e = (ds, ss, p)
    * iso_exps env es = (ds, ss, ps)
    * iso_lv env lv = (ds, ss, p)
    *
    * decomposes a potentially effectful expression e (expression es,
    * lvalue lv) into a sequence of variable declarations ds, a sequence of 
    * statements ss and a pure expression p.  The semantics of e in C0 is
    * achieved by executing ds, then ss, then return the value of p.
    * This code is currently as straightforward as possible.
    * With some purity analysis, it could produce more natural-looking C.
    *)
   fun iso_exp env (e as A.Var(id)) = ([], e)
     | iso_exp env (e as A.IntConst(w)) = ([], e)
     | iso_exp env (e as A.StringConst(s)) = ([], e)
     | iso_exp env (e as A.CharConst(c)) = ([], e)
     | iso_exp env (e as A.True) = ([], e)
     | iso_exp env (e as A.False) = ([], e)
     | iso_exp env (e as A.Null) = ([], e)
     | iso_exp env (e as A.OpExp(A.SUB, [e1, e2])) =
       let val (ss1, p1) = iso_exp env e1
	   val (ss2, p2) = iso_exp env e2
	   val tp = Syn.syn_exp env e
	   val (sd, t) = new_tmp_init(tp, A.OpExp(A.SUB, [p1, p2]))
       in
	   (ss1 @ ss2 @ [sd], t)
       end
     | iso_exp env (e as A.OpExp(A.DEREF, [e1])) =
       let val (ss1, p1) = iso_exp env e1
	   val tp = Syn.syn_exp env e
	   val (sd, t) = new_tmp_init(tp, A.OpExp(A.DEREF, [p1]))
       in
	   (ss1 @ [sd], t)
       end
     | iso_exp env (e as A.OpExp(A.DIVIDEDBY, [e1,e2])) =
       let val (ss1, p1) = iso_exp env e1
	   val (ss2, p2) = iso_exp env e2
       in
	   if is_safe_div p2
	   then (ss1 @ ss2, A.OpExp(A.DIVIDEDBY, [p1, p2]))
	   else let
		   val tp = Syn.syn_exp env e
		   val (sd, t) = new_tmp_init(tp, A.OpExp(A.DIVIDEDBY, [p1, p2]))
	       in
		   (ss1 @ ss2 @ [sd], t)
	       end 
       end
     | iso_exp env (e as A.OpExp(A.MODULO, [e1,e2])) =
       let val (ss1, p1) = iso_exp env e1
	   val (ss2, p2) = iso_exp env e2
       in
	   if is_safe_div p2
	   then (ss1 @ ss2, A.OpExp(A.MODULO, [p1, p2]))
	   else let
		   val tp = Syn.syn_exp env e
		   val (sd, t) = new_tmp_init(tp, A.OpExp(A.MODULO, [p1, p2]))
	       in
		   (ss1 @ ss2 @ [sd], t)
	       end 
       end
     (* A.SHIFTLEFT and A.SHIFTRIGHT may translate to function calls,
      * but the calls are pure *)
     | iso_exp env (A.OpExp(A.LOGAND, [e1, e2])) =
         iso_exp env (A.OpExp(A.COND, [e1, e2, A.False]))
     | iso_exp env (A.OpExp(A.LOGOR, [e1, e2])) =
         iso_exp env (A.OpExp(A.COND, [e1, A.True, e2]))
     | iso_exp env (e as A.OpExp(A.COND, [e1, e2, e3])) =
       let val (ss1, p1) = iso_exp env e1
           val (ss2, p2) = iso_exp env e2
           val (ss3, p3) = iso_exp env e3
	   val (d, t) = Syn.new_tmp(Syn.syn_exp env e)
           (* if e = (e1 ? NULL : NULL) then t has type void*
            * this is okay, because C will coerce to any type tp*,
            * an dereferencing at type void* is disallowed in C0 *)
        in
	   case (ss2, ss3, p2, p3)
	    of ([], [], _, A.False) => (ss1, A.OpExp(A.LOGAND, [p1, p2]))
	     | ([], [], A.True, _) => (ss1, A.OpExp(A.LOGOR, [p1, p3]))
	     | ([], [], _, _) => (ss1, A.OpExp(A.COND, [p1, p2, p3]))
	     | _ => ([A.StmDecl(d)] @ ss1
		     @ [A.If(p1, A.Seq(nil, ss2 @ [A.Assign(NONE, t, p2)]),
			         A.Seq(nil, ss3 @ [A.Assign(NONE, t, p3)]))],
		     t)
       end
     | iso_exp env (A.OpExp(oper, [e1])) =
       let val (ss1, p1) = iso_exp env e1
       in (ss1, A.OpExp(oper, [p1])) end
     | iso_exp env (A.OpExp(oper, [e1,e2])) =
       let val (ss1, p1) = iso_exp env e1
	   val (ss2, p2) = iso_exp env e2
       in (ss1 @ ss2, A.OpExp(oper, [p1, p2])) end
     | iso_exp env (e as A.Select(e1, f)) =
       (* e1 could have large type; isolate as lval *)
       (* iso_select env (A.Select(e1, f)) *)
       let val (ss1, p1) = iso_lv env e1
	   val tp = Syn.syn_exp env e
           val (ds, t) = new_tmp_init(tp, A.Select(p1, f))
        in (ss1 @ [ds], t) end
     | iso_exp env (e as A.FunCall(g, es)) =
       let val (ss, ps) = iso_exps env es
	   val tp = Syn.syn_exp env e
	   val (ds, t) = new_tmp_init(tp, A.FunCall(g, ps))
       in (ss @ [ds], t) end
     | iso_exp env (e as A.Alloc(tp)) =
       let val (ds, t) = new_tmp_init(Syn.syn_exp env e, A.Alloc(tp))
       in ([ds], t) end
     | iso_exp env (e as A.AllocArray(tp, e1)) =
       let val (ss1, p1) = iso_exp env e1
	   val (ds,t) = new_tmp_init(Syn.syn_exp env e, A.AllocArray(tp, p1))
       in (ss1 @ [ds], t) end
     | iso_exp env (e as A.Result) = ([], e)
     | iso_exp env (A.Length(e1)) =
       (* \length(p1) has no effect *)
       let val (ss1, p1) = iso_exp env e1
       in (ss1, A.Length(p1)) end
     | iso_exp env (e as A.Old(e1)) =
       (* \old(e1) is not executed as given; leave alone for now *)
         ([], e)
     | iso_exp env (A.Marked(marked_exp)) =
         iso_exp env (Mark.data marked_exp)

    and iso_exps env nil = ([], [])
      | iso_exps env (e::es) =
	let val (ss1, p) = iso_exp env e
	    val (ss2, ps) = iso_exps env es
	in
	    (ss1 @ ss2, p::ps)
	end

    (* iso_lv env lv = (ds, ss, p) [see iso_exp above] is complicated
     * by the fact that some subexpressions e have large type tp, so they
     * cannot directly turned into a declaration tp _tmp_ = e;
     * We use this not just for lvalues, but generally expressions with
     * a large type, so the function name is not precise. *)
    and iso_lv env (e as A.Var(x)) = ([], e)
      | iso_lv env (A.OpExp(A.SUB, [lv1, e2])) =
        (* lv1 has small type t[]; isolate as an expression *)
	let val (ss1, lv1') = iso_exp env lv1 (* Dec 2010, -fp *)
	    val (ss2, p2) = iso_exp env e2
	in
	    (ss1 @ ss2, A.OpExp(A.SUB, [lv1', p2]))
	end
      | iso_lv env (A.OpExp(A.DEREF, [lv1])) =
        (* lv1 has small type t*; isolate as an expression *)
	let val (ss1, lv1') = iso_exp env lv1 (* Dec 2010, -fp *)
	in (ss1, A.OpExp(A.DEREF, [lv1'])) end
      | iso_lv env (A.Select(lv1, f2)) =
        (* lv1 could have large type; must isolate as an lval *)
	let val (ss1, lv1') = iso_lv env lv1
	in (ss1, A.Select(lv1', f2)) end
      | iso_lv env (A.Marked(marked_exp)) =
	  iso_lv env (Mark.data marked_exp)
      | iso_lv env (e) =
        (* any other form of expression has small type *)
	(* this case is necessary for expressions such as g()->f *)
	iso_exp env e

    (* iso_stm env s = ss' where the effect of s is the same
     * as executing ss'.  Declarations d are turned into statements
     * A.StmDecl(d') so that we can easily mix declarations and
     * ordinary statements and initalize temporary variables
     * at the point they are declared *)
    fun iso_stm env (A.Assign(oper_opt, lv, e)) =
	let val (ss1, lv1) = iso_lv env lv
	    val tp1 = Syn.syn_exp env lv
	in
	    iso_assign env oper_opt (ss1, lv1) tp1 e
	end
      | iso_stm env (A.Exp(e)) = iso_stmexp env e
      | iso_stm env (A.Seq(ds, ss)) =
	let val (ss1, env') = iso_decls env ds
	    val ss2 = iso_stms env' ss
	in
            (* preserve scope to avoid name clashes in the target code *)
	    ([A.Seq([], ss1 @ ss2)])
	end
      | iso_stm env (A.StmDecl(d)) =
	  (* StmDecl in source has empty scope at this point *)
          iso_stm env (A.Seq([d], []))
      | iso_stm env (A.If(e, s1, s2)) =
	let val (ss, p) = iso_exp env e
	    val ss1 = iso_stm env s1
	    val ss2 = iso_stm env s2
	in
	    (ss @ [A.If(p, A.Seq([],ss1), A.Seq([],ss2))])
	end
      | iso_stm env (A.While(e1, invs, s2)) = (* ignore invariants here *)
	let val (ss1, p1) = iso_exp env e1
	    val ss2 = iso_stm env s2
            (* ss1 must be executed every time before testing the
	     * exit condition. We simplify the case there e1 has
             * no effects (ss1 = []) *)
	in
	    case ss1
	     of [] => [A.While(p1, invs, A.Seq([], ss2))]
	      | _ => [A.While(A.True, invs,
			      A.Seq([], ss1
					@ [A.If(p1, A.Seq([],[]),
						A.Seq([],[A.Break]))]
					@ ss2))]
	end
      | iso_stm env (A.Continue) = [A.Continue]
      | iso_stm env (A.Break) = [A.Break]
      | iso_stm env (A.Return(SOME(e))) =
	let val (ss, p) = iso_exp env e
	in
	    (ss @ [A.Return(SOME(p))])
	end
      | iso_stm env (A.Return(NONE)) = [A.Return(NONE)]
      | iso_stm env (A.Assert(e1, e2s)) =
	let val (ss1, p1) = iso_exp env e1
	    val (ss2, p2s) = iso_exps env e2s
	in
	    (ss1 @ ss2 @ [A.Assert(p1, p2s)])
	end
      | iso_stm env (A.Anno(specs)) = (* ignore specs here *)
	  []
      | iso_stm env (A.Markeds(marked_stm)) =
	  iso_stm env (Mark.data marked_stm)

    and iso_stms env nil = nil
      | iso_stms env (s::ss) =
	let val ss1 = iso_stm env s
	    val ss2 = iso_stms env ss
	in ss1 @ ss2 end

    (* iso_decls env ds = (ss', env'), where ss' has the same effect
     * as ds, and env' is the extension of env by declarations ds *)
    and iso_decls env (A.VarDecl(id, tp, NONE, ext)::ds) =
	let val (ss', env') = iso_decls (Symbol.bind env (id, tp)) ds
	in ([A.StmDecl(A.VarDecl(id, tp, NONE, ext))] @ ss', env') end
      | iso_decls env (A.VarDecl(id, tp, SOME(e), ext)::ds) =
	let val (ss1, p1) = iso_exp env e
	    val (ss2, env') = iso_decls (Symbol.bind env (id, tp)) ds
	in (ss1 @ [A.StmDecl(A.VarDecl(id, tp, SOME(p1), ext))] @ ss2,
	    env')
	end
      | iso_decls env nil = (nil, env)

    (* isolating a top-level function call is special
     * because if it has return type void we cannot bind
     * a temporary variable to its value *)
    and iso_stmexp env (A.FunCall(g, es)) =
	let val (ss, ps) = iso_exps env es
	in (ss @ [A.Exp(A.FunCall(g, ps))]) end
      | iso_stmexp env (A.Marked(marked_exp)) =
	  iso_stmexp env (Mark.data marked_exp)
      | iso_stmexp env e =
	let val (ss, p) = iso_exp env e
	in (ss @ [A.Exp(p)]) end

    (* iso_assign env oper_opt (ss1, lv1) tp1 e2 = ss
     * where ss has the same effect as ss1 ; lv1 = e2.
     * We assume env, decls(ss1) |- lv1 : tp1 and env |- e2 : tp1.
     * The difficult part is to guarantee left-to-right evaluation
     * of an assignment, because in A[e1] = e2, e1 must be evaluated
     * before e2, but C does not guarantee this.  Also, the out-of-bounds
     * check for A[e1] should happen before the evaluation of e2.
     * In this example, we start with A[e1] ~> ss1 ; lv1
     * and then name a pointer to the address of lv1:
     * tp1* t = &(lv1); ss2; *t = p2; where e2 ~> ss2 ; p2
     *)
    and iso_assign env (oper_opt as (SOME _)) (ss1, lv1) tp1 e2 =
	(* compound assignment lv1 <op>= e2 ok, since lv1 pure *)
	let
	    val (ss2, p2) = iso_exp env e2
	in
	    (ss1 @ ss2 @ [A.Assign(oper_opt, lv1, p2)])
	end
      | iso_assign env (NONE) (ss1, lv1 as A.Var _) tp1 e2 =
	(* x = e2 ok, since x has no effect *)
	let
	    val (ss2, p2) = iso_exp env e2
	in
	    (ss1 @ ss2 @ [A.Assign(NONE, lv1, p2)])
	end
      | iso_assign env (NONE) (ss1, lv1 as A.OpExp(A.DEREF, _)) tp1 e2 =
	(* *lv1' = e2 ok, since lv1' has no effect, and *lv1 is not computed
         * as a lvalue *)
        let
	    val (ss2, p2) = iso_exp env e2
	in
	    (ss1 @ ss2 @ [A.Assign(NONE, lv1, p2)])
	end
      | iso_assign env (NONE) (ss1, lv1) tp1 e2 =
	 (* lv1 = A[p1] or lv1 = lv1'.f requires transformation to guarantee
          * left-to-right.  Complication is that lv1' may have large type.
	  *)
	let
            (* use tp1, because type of e1 may be void* if NULL *)
	    val (d, t) = Syn.new_tmp (A.Pointer(tp1))
	    val (ss2, p2) = iso_exp env e2
	in
	    (ss1 @ [A.StmDecl(d)]		 (* ss1 ; tp1* t; *)
	     @ [A.Assign(SOME(A.DEREF), t, lv1)] (* t <*>= lv1; meaning t = &lv1; *)
	     @ ss2 @ [A.Assign(NONE, A.OpExp(A.DEREF, [t]), p2)]) (* ss2 ; *t = p2; *)
	end

    (*
     * Printing, under the assumption that effects have been isolated
     *)
    fun is_external g =
	( case Symtab.lookup g
	   of SOME(A.Function(g', rtp, params, bodyOpt, specs, is_extern, ext)) => is_extern
	    | _ => false )

    (* add_stmdecl env s = env', adding declaration d to env in case
     * s is a declaration-as-statement d *)
    fun add_stmdecl env (A.StmDecl(A.VarDecl(id, tp, _, _))) = Symbol.bind env (id, tp)
      | add_stmdecl env _ = env

    (* indent n str = str', only to be used for string
     * at beginning of line.  Used to make output more readable. *)
    fun indent n str = (StringCvt.padLeft #" " n "") ^ str

    (* is_nop s = true, if s is a nop, or sequence of nops.
     * Used to make output more readable. *)
    fun is_nop (A.Seq([], ss)) = is_nops ss
      | is_nop _ = false
    and is_nops nil = true
      | is_nops (s::ss) = is_nop s andalso is_nops ss

    (* Name mangling, to avoid conflict with C keywords and
     * with each other.  Readability of code could be improved
     * by only doing this when necessary *)
    fun pp_field f = "_c0_" ^ Symbol.name f
    fun pp_struct s = "struct _c0_" ^ Symbol.name s
    fun pp_typename t = "_c0_" ^ Symbol.name t
    fun pp_var id = "_c0v_" ^ Symbol.name id  (* not sure if this could be _c0_ *)
    fun pp_fun id =
	let
	    val name = Symbol.name id
	in
	    if is_external id
	    then name
	    else "_c0_" ^ name
	end
    fun pp_extfun id = Symbol.name id  (* extern function: do not munge *)

    (* pp_tp tp = str, converting tp to C equivalent *)
    fun pp_tp (A.Int) = "int"	       (* should be: int32_t in <stdint.h>? *)
      | pp_tp (A.Bool) = "bool"	       (* in <stdbool.h> *)
      | pp_tp (A.String) = "c0_string" (* "abstract", typically char* *)
      | pp_tp (A.Char) = "char"	       (* "abstract", typically char *)
      | pp_tp (A.Pointer(tp)) = pp_tp tp ^ "*"
      | pp_tp (A.Array(tp)) = "cc0_array(" ^ pp_tp tp ^ ")" (* typically, struct of length and tp* *)
      | pp_tp (A.StructName(s)) = pp_struct s
      | pp_tp (A.TypeName(t)) = pp_typename t
      | pp_tp (A.Void) = "void"        (* for function return *)
      | pp_tp (A.Any) = "void"	       (* for NULL, which has type A.Pointer(A.Any) *)

    (* pp_oper oper = str, converting operator to C equivalent *)
    fun pp_oper A.LOGNOT = "!"
      | pp_oper A.COMPLEMENT = "~"
      | pp_oper A.NEGATIVE = "-"
      | pp_oper A.DEREF = "*"
      | pp_oper A.TIMES = "*"
      | pp_oper A.DIVIDEDBY = "/"   (* for save div *)
      | pp_oper A.MODULO = "%"	    (* for safe mod *)
      | pp_oper A.PLUS = "+"
      | pp_oper A.MINUS = "-"
      | pp_oper A.SHIFTLEFT = "<<"  (* for safe sal *)
      | pp_oper A.SHIFTRIGHT = ">>" (* for safe sar *)
      | pp_oper A.LESS = "<"
      | pp_oper A.LEQ = "<="
      | pp_oper A.GREATER = ">"
      | pp_oper A.GEQ = ">="
      | pp_oper A.EQ = "=="
      | pp_oper A.NOTEQ = "!="
      | pp_oper A.AND = "&"
      | pp_oper A.XOR = "^"
      | pp_oper A.OR = "|"
      | pp_oper A.LOGAND = "&&"
      | pp_oper A.LOGOR = "||"

    (* pp_exp env e = str, converting expression to C equivalent.
     * Uses only one line and parentheses liberally to disambiguate.
     * Also uses various macros to allow safe and unsafe runtimes.
     * See c0/include/cc0lib.h and c0/include/c0rt.h *)
    fun pp_exp env (A.Var(id)) = pp_var id
      | pp_exp env (A.IntConst(w)) = (* bug workaround for gcc -fwrapv, Jan 22, 2012 *)
	if (w = Word32Signed.TMIN) then "(-2147483647-1)" else Word32Signed.toString w
      | pp_exp env (A.StringConst(s)) = "c0_string_fromliteral(\"" ^ String.toCString s ^ "\")"
      | pp_exp env (A.CharConst(c)) = "'" ^ Char.toCString c ^ "'"
      | pp_exp env (A.True) = "true"
      | pp_exp env (A.False) = "false"
      | pp_exp env (A.Null) = "NULL"
      | pp_exp env (A.OpExp(oper as A.DIVIDEDBY, [e1, e2])) =
	if is_safe_div e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "_idiv(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(oper as A.MODULO, [e1, e2])) =
	if is_safe_div e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "_imod(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(oper as A.SHIFTLEFT, [e1, e2])) =
	if is_safe_shift e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "_sal(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(oper as A.SHIFTRIGHT, [e1, e2])) =
	if is_safe_shift e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "_sar(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(A.SUB, [e1,e2])) =
	let val A.Array(tp) = Syn.syn_exp_expd env e1
	in
	    "cc0_array_sub(" ^ pp_tp tp ^ "," ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
	end
      | pp_exp env (A.OpExp(A.DEREF, [e1])) =
	let val A.Pointer(tp) = Syn.syn_exp_expd env e1
	in "cc0_deref(" ^ pp_tp tp ^ ", " ^ pp_exp env e1 ^ ")" end
      | pp_exp env (A.OpExp(A.COND, [e1, e2, e3])) =
        "(" ^ pp_exp env e1 ^ " ? " ^ pp_exp env e2 ^ " : " ^ pp_exp env e3 ^ ")"
      | pp_exp env (A.OpExp(oper, [e])) =
	pp_oper oper ^ "(" ^ pp_exp env e ^ ")"
      | pp_exp env (A.OpExp(oper, [e1,e2])) =
	"(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.Select(e, f)) =
	"(" ^ pp_exp env e ^ ")." ^ pp_field f
      | pp_exp env (A.FunCall(id, es)) =
	  pp_fun id ^ "(" ^ pp_exps env es ^ ")"
      | pp_exp env (A.Alloc(tp)) = "cc0_alloc(" ^ pp_tp tp ^ ")"
      | pp_exp env (A.AllocArray(tp, e)) = "cc0_alloc_array(" ^ pp_tp tp ^ "," ^ pp_exp env e ^ ")"
      | pp_exp env (A.Result) = (* should be impossible, except in comment *)
	  "\\result"
      | pp_exp env (A.Length(e)) = "c0_array_length(" ^ pp_exp env e ^ ")"
      | pp_exp env (A.Old(e)) = (* should be impossible, except in comment *)
	  "\\old(" ^ pp_exp env e ^ ")"
      | pp_exp env (A.Marked(marked_exp)) =
	  pp_exp env (Mark.data marked_exp)

    and pp_exps env nil = ""
      | pp_exps env (e::nil) = pp_exp env e
      | pp_exps env (e::es) = pp_exp env e ^ ", " ^ pp_exps env es

    and pp_stringlist env nil = "\"\""
      | pp_stringlist env (e::nil) = pp_exp env e
      | pp_stringlist env (e::es) =
	"c0_string_join(" ^ pp_exp env e ^ ", " ^ pp_stringlist env es ^ ")"

    (* for unsigned version, for oper = A.LESS, A.LEQ, A.GREATER, A.GEQ:
     and pp_comparison env (A.OpExp(oper, [e1, e2])) =
	 "(((int)" ^ pp_exp env e1 ^ ")" ^ pp_oper oper ^ "((int)"
	 ^ pp_exp env e2 ^ "))"
     *)

    fun pp_assign_effect_op env (cname, A.Var(id), e) =
	  pp_var id ^ " = " ^ cname ^ "(" ^ pp_var id ^ "," ^ pp_exp env e ^ ");"
      | pp_assign_effect_op env (cname, A.Marked(marked_exp), e) =
	  pp_assign_effect_op env (cname, Mark.data marked_exp, e)
      | pp_assign_effect_op env (cname, lv, e) = (* lv != x *)
	  cname ^ "_asn(&" ^ pp_exp env lv ^ "," ^ pp_exp env e ^ ");"

    fun pp_assign env (A.Assign(NONE, lv, e)) =
	  pp_exp env lv ^ " = " ^ pp_exp env e ^ ";"
      | pp_assign env (A.Assign(SOME(A.DEREF), lv, e)) =
          (* hack: x <*>= e means x = &e *)
	  pp_exp env lv ^ " = " ^ "&(" ^ pp_exp env e ^ ")" ^ ";"
      | pp_assign env (A.Assign(SOME(A.DIVIDEDBY), lv, e)) =
	  pp_assign_effect_op env ("_idiv", lv, e)
      | pp_assign env (A.Assign(SOME(A.MODULO), lv, e)) =
	  pp_assign_effect_op env ("_imod", lv, e)
      | pp_assign env (A.Assign(SOME(A.SHIFTLEFT), lv, e)) =
	  pp_assign_effect_op env ("_sal", lv, e)
      | pp_assign env (A.Assign(SOME(A.SHIFTRIGHT), lv, e)) =
	  pp_assign_effect_op env ("_sar", lv, e)
      | pp_assign env (A.Assign(SOME(oper), lv, e)) =
	  pp_exp env lv ^ " " ^ pp_oper oper ^ "= " ^ pp_exp env e ^ ";"

    (* pp_stm n env s = str
     * pp_stms n env ss = str
     * pp_decl n env d = str
     * pp_decls n env ds = str
     * Convert statement(s) or declaration(s) to string, in
     * environment env, indenting new lines n spaces.
     * Assume body of while-loop and branches of conditional
     * are sequences, which is guaranteed by iso_<cat>.
     * Also, statements are free of for-loops *)
    fun pp_stm n env (s as A.Assign (oper_opt, lv, e)) =
          indent n (pp_assign env s)
      | pp_stm n env (A.Exp(e)) =
	  (* effects have been isolated *)
	  indent n (pp_exp env e ^ ";")
      | pp_stm n env (A.Seq(nil, nil)) =
	  indent n "{ }"
      | pp_stm n env (A.Seq(nil, [s' as A.Seq _])) =
	  (* compress nested sequences *)
	  pp_stm n env s'
      | pp_stm n env (A.Seq(ds, ss)) =
	let val env' = Syn.syn_decls env ds
	in
	    indent n "{\n"
	    ^ pp_decls (n+2) env ds
	    ^ pp_stms (n+2) env' ss
	    ^ indent n "}"
	end
      | pp_stm n env (A.StmDecl(d)) =
	let val env' = Syn.syn_decls env [d]
	in
	    pp_decl n env d
	end
      | pp_stm n env (A.If(e, A.Seq([], ss1), A.Seq([], ss2))) =
	indent n ("if (" ^ pp_exp env e ^ ") {\n")
	^ pp_stms (n+2) env ss1
	^ indent n "}"
        ^ (if is_nops ss2
	   then "" (* ok, since braces delimit scope? *)
	   else " else {\n" ^ pp_stms (n+2) env ss2
		^ indent n "}")
      | pp_stm n env (A.While(e, _, A.Seq([], ss))) =
	indent n ("while (" ^ pp_exp env e ^ ") {\n")
	^ pp_stms (n+2) env ss
	^ indent n "}"
      (* no A.For *)
      | pp_stm n env (A.Continue) = indent n "continue;"
      | pp_stm n env (A.Break) = indent n "break;"
      | pp_stm n env (A.Return(SOME(e))) =
	  indent n ("return " ^ pp_exp env e ^ ";")
      | pp_stm n env (A.Return(NONE)) =
	  indent n "return;"
      | pp_stm n env (A.Assert(e1, e2s)) =
          (* We reduce e2s to a single string by concatenation, to avoid
           * variadic functions or macros *)
	  indent n ("cc0_assert(" ^ pp_exp env e1 ^ ", " ^ pp_stringlist env e2s ^ ");")
      | pp_stm n env (A.Anno(specs)) = (* should not arise *)
	  indent n ";"
      | pp_stm n env (A.Markeds(marked_stm)) =
	  pp_stm n env (Mark.data marked_stm)

    and pp_stms n env nil = ""
      | pp_stms n env (A.Seq([],ss1)::nil) =
	  (* avoid spurious blocks, tail must be nil to avoid incorrect
           * mixing of scopes *)
	  pp_stms n env ss1
      | pp_stms n env (s::ss) =
          (* update environment if s is declaration d *)
	  pp_stm n env s ^ "\n"
	  ^ pp_stms n (add_stmdecl env s) ss

    and pp_decl n env (A.VarDecl(id, tp, NONE, ext)) =
	  indent n (pp_tp tp ^ " " ^ pp_var id ^ ";")
      | pp_decl n env (A.VarDecl(id, tp, SOME(e), ext)) =
	  indent n (pp_tp tp ^ " " ^ pp_var id ^ " = " ^ pp_exp env e ^ ";")

    and pp_decls n env nil = ""
      | pp_decls n env (d::ds) =
	  pp_decl n env d ^ "\n"
	  ^ pp_decls n (Syn.syn_decls env [d]) ds

    fun pp_param (id, tp) =
	  pp_tp tp ^ " " ^ pp_var id

    (* pp_params ds = str, converting parameter list to string *)
    fun pp_params nil = ""
      | pp_params (A.VarDecl(id,tp,NONE,ext)::nil) = pp_param (id, tp)
      | pp_params (A.VarDecl(id,tp,NONE,ext)::params) =
	  pp_param (id, tp) ^ ", " ^ pp_params params

    (* pp_fields n fields = str, converting list of fields to string *)
    fun pp_fields n nil = ""
      | pp_fields n (A.Field(f,tp,ext)::fields) =
	  indent n (pp_tp tp ^ " " ^ pp_field f ^ ";\n")
	  ^ pp_fields n fields

    (* pp_gdecl gdecl = str
     * pp_gdecls gdecls = str
     * converting global declaration to string *)
    fun pp_gdecl (A.Struct(s, NONE, is_external, ext)) =
	  pp_struct s ^ ";\n"
      | pp_gdecl (A.Struct(s, SOME(fields), is_external, ext)) =
	  pp_struct s ^ " {\n" ^ pp_fields 2 fields ^ "};\n"
      | pp_gdecl (A.Function(g, result, params, NONE, specs, is_extern, ext)) =
	  (if is_extern then "extern " else "")
	  ^ pp_tp result ^ " " ^ pp_fun g ^ "(" ^ pp_params params ^ ");\n"
      | pp_gdecl (A.Function(g, rtp, params, SOME(s), _, _, ext)) =
	let
	    val env0 = Syn.syn_decls Symbol.empty params
	    val env1 = Symbol.bind env0 (Symbol.symbol "\\result", rtp)
	    val ss = iso_stm env1 s
	in (* newline before function definitions *)
	    "\n" ^ pp_tp rtp ^ " " ^ pp_fun g ^ "("
	    ^ pp_params params ^ ") {\n"
	    ^ pp_stms 2 env1 ss
	    ^ "}\n"
	end
      | pp_gdecl (A.TypeDef(aid, tp, ext)) =
	"typedef " ^ pp_tp tp ^ " " ^ pp_typename aid ^ ";\n"

      (* pragmas are included as comments in C file *)
      | pp_gdecl (A.Pragma(A.UseLib(libname, SOME(gdecls)), ext)) =
	"\n//#use <" ^ libname ^ ">\n"
	^ pp_gdecls gdecls
	^ "// end <" ^ libname ^ ">\n"
      | pp_gdecl (A.Pragma(A.UseFile(filename, SOME(gdecls)), ext)) =
	"\n//#use \"" ^ filename ^ "\"\n"
	^ pp_gdecls gdecls
	^ "// end \"" ^ filename ^ "\"\n"
      | pp_gdecl (A.Pragma(A.Raw(pname, pargs), ext)) =
	"\n//" ^ pname ^ pargs ^ "\n"

    and pp_gdecls nil = ""
      | pp_gdecls (gdecl::gdecls) =
          pp_gdecl gdecl ^ pp_gdecls gdecls

    (* pp_program gdecls include_files opt_level = str
     * Convert program consisting of gdecls to a string, including
     * include_files.  Optimization level opt_level is currently
     * unused *)
    fun pp_program gdecls include_files opt_level =
          String.concat 
            (map (fn include_file => "#include \"" ^ include_file ^ "\"\n")
                 include_files)
          ^ pp_gdecls gdecls

end
