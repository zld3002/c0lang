signature ISOLATE = 
sig
  val iso_exp : Ast.tp Symbol.table -> Ast.exp -> (Ast.stm list * Ast.exp)
  val iso_stm : Ast.tp Symbol.table -> Ast.stm -> Ast.stm list
end

structure Isolate :> ISOLATE = 
struct
   structure A = Ast

   (* new statement "tp _tmp_<n> = e;" *)
   fun new_tmp_init (tp, e) ext =
       let val (d, t) = Syn.new_tmp_init (tp, e) ext
       in (A.StmDecl(d), t) end

   fun marks s ext = A.Markeds (Mark.mark'(s,ext))

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
   
   (* iso_exp env e ext = (ss, p)
    * iso_exps env es ext = (ss, ps)
    * iso_lv env lv ext = (ss, p, ext')
    *
    * decomposes a potentially effectful expression e (expression es,
    * lvalue lv) into a sequence of variable declarations ds, a sequence of 
    * statements ss and a pure expression p.  The semantics of e in C0 is
    * achieved by executing ds, then ss, then return the value of p.
    * This code is currently as straightforward as possible.
    * With some purity analysis, it could produce more natural-looking C.
    *
    * note: ext is currently not used, except for iso_lv
    *)
   fun iso_exp env (e as A.Var(id)) ext = ([], e)
     | iso_exp env (e as A.IntConst(w)) ext = ([], e)
     | iso_exp env (e as A.StringConst(s)) ext = ([], e)
     | iso_exp env (e as A.CharConst(c)) ext = ([], e)
     | iso_exp env (e as A.True) ext = ([], e)
     | iso_exp env (e as A.False) ext = ([], e)
     | iso_exp env (e as A.Null) ext = ([], e)
     | iso_exp env (e as A.OpExp(A.SUB, [e1, e2])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
	   val (ss2, p2) = iso_exp env e2 ext
	   val tp = Syn.syn_exp env e
	   val (sd, t) = new_tmp_init (tp, A.OpExp(A.SUB, [p1, p2])) ext
       in
	   (ss1 @ ss2 @ [sd], t)
       end
     | iso_exp env (e as A.OpExp(A.DEREF, [e1])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
	   val tp = Syn.syn_exp env e
	   val (sd, t) = new_tmp_init (tp, A.OpExp(A.DEREF, [p1])) ext
       in
	   (ss1 @ [sd], t)
       end
     | iso_exp env (e as A.OpExp(A.DIVIDEDBY, [e1,e2])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
	   val (ss2, p2) = iso_exp env e2 ext
       in
	   if is_safe_div p2
	   then (ss1 @ ss2, A.OpExp(A.DIVIDEDBY, [p1, p2]))
	   else let
		   val tp = Syn.syn_exp env e
		   val (sd, t) = new_tmp_init (tp, A.OpExp(A.DIVIDEDBY, [p1, p2])) ext
	       in
		   (ss1 @ ss2 @ [sd], t)
	       end 
       end
     | iso_exp env (e as A.OpExp(A.MODULO, [e1,e2])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
	   val (ss2, p2) = iso_exp env e2 ext
       in
	   if is_safe_div p2
	   then (ss1 @ ss2, A.OpExp(A.MODULO, [p1, p2]))
	   else let
		   val tp = Syn.syn_exp env e
		   val (sd, t) = new_tmp_init (tp, A.OpExp(A.MODULO, [p1, p2])) ext
	       in
		   (ss1 @ ss2 @ [sd], t)
	       end 
       end
     (* A.SHIFTLEFT and A.SHIFTRIGHT may translate to function calls,
      * but the calls are pure *)
     | iso_exp env (A.OpExp(A.LOGAND, [e1, e2])) ext =
         iso_exp env (A.OpExp(A.COND, [e1, e2, A.False])) ext
     | iso_exp env (A.OpExp(A.LOGOR, [e1, e2])) ext =
         iso_exp env (A.OpExp(A.COND, [e1, A.True, e2])) ext
     | iso_exp env (e as A.OpExp(A.COND, [e1, e2, e3])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
           val (ss2, p2) = iso_exp env e2 ext
           val (ss3, p3) = iso_exp env e3 ext
	   val (d, t) = Syn.new_tmp (Syn.syn_exp env e) ext
           (* if e = (e1 ? NULL : NULL) then t has type void*
            * this is okay, because C will coerce to any type tp*,
            * and dereferencing at type void* is disallowed in C0 *)
        in
	   case (ss2, ss3, p2, p3)
	    of ([], [], _, A.False) => (ss1, A.OpExp(A.LOGAND, [p1, p2]))
	     | ([], [], A.True, _) => (ss1, A.OpExp(A.LOGOR, [p1, p3]))
	     | ([], [], _, _) => (ss1, A.OpExp(A.COND, [p1, p2, p3]))
	     | _ => ([A.StmDecl(d)] @ ss1
		     @ [marks
			(A.If(p1, A.Seq(nil, ss2 @ [A.Assign(NONE, t, p2)]),
			         A.Seq(nil, ss3 @ [A.Assign(NONE, t, p3)])))
		       ext],
		     t)
       end
     | iso_exp env (A.OpExp(oper, [e1])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
       in (ss1, A.OpExp(oper, [p1])) end
     | iso_exp env (A.OpExp(oper, [e1,e2])) ext =
       let val (ss1, p1) = iso_exp env e1 ext
	   val (ss2, p2) = iso_exp env e2 ext
       in (ss1 @ ss2, A.OpExp(oper, [p1, p2])) end
     | iso_exp env (e as A.Select(e1, f)) ext =
       (* e1 could have large type; isolate as lval *)
       (* iso_select env (A.Select(e1, f)) *)
       let val (ss1, p1, ext1) = iso_lv env e1 ext (* ignore ext1 here *)
	   val tp = Syn.syn_exp env e
           val (ds, t) = new_tmp_init (tp, A.Select(p1, f)) ext
        in (ss1 @ [ds], t) end
     | iso_exp env (e as A.FunCall(g, es)) ext =
       let val (ss, ps) = iso_exps env es ext
	   val tp = Syn.syn_exp env e
	   val (ds, t) = new_tmp_init (tp, A.FunCall(g, ps)) ext
       in (ss @ [ds], t) end
     | iso_exp env (e as A.Alloc(tp)) ext =
       let val (ds, t) = new_tmp_init (Syn.syn_exp env e, A.Alloc(tp)) ext
       in ([ds], t) end
     | iso_exp env (e as A.AllocArray(tp, e1)) ext =
       let val (ss1, p1) = iso_exp env e1 ext
	   val (ds,t) = new_tmp_init (Syn.syn_exp env e, A.AllocArray(tp, p1)) ext
       in (ss1 @ [ds], t) end
     | iso_exp env (e as A.Result) ext = ([], e)
     | iso_exp env (A.Length(e1)) ext =
       (* \length(p1) has no effect *)
       let val (ss1, p1) = iso_exp env e1 ext
       in (ss1, A.Length(p1)) end
     | iso_exp env (e as A.Old(e1)) ext =
       (* \old(e1) is not executed as given; leave alone for now *)
         ([], e)
     | iso_exp env (A.Marked(marked_exp)) ext =
         (* do not preserve mark here, since result is statement list
          * followed by pure expression *)
         iso_exp env (Mark.data marked_exp) (Mark.ext marked_exp)

    and iso_exps env nil ext = ([], [])
      | iso_exps env (e::es) ext =
	let val (ss1, p) = iso_exp env e ext
	    val (ss2, ps) = iso_exps env es ext
	in
	    (ss1 @ ss2, p::ps)
	end
    
    (* iso_lv env lv ext = (ss, p, ext') [see iso_exp above] is complicated
     * by the fact that some subexpressions e have large type tp, so they
     * cannot directly turned into a declaration tp _tmp_ = e;
     * We use this not just for lvalues, but generally expressions with
     * a large type, so the function name is not precise. *)
    and iso_lv env (e as A.Var(x)) ext = ([], e, ext)
      | iso_lv env (A.OpExp(A.SUB, [lv1, e2])) ext =
        (* lv1 has small type t[]; isolate as an expression *)
	let val (ss1, lv1') = iso_exp env lv1 ext (* Dec 2010, -fp *)
	    val (ss2, p2) = iso_exp env e2 ext
	in
	    (ss1 @ ss2, A.OpExp(A.SUB, [lv1', p2]), ext)
	end
      | iso_lv env (A.OpExp(A.DEREF, [lv1])) ext =
        (* lv1 has small type t*; isolate as an expression *)
	let val (ss1, lv1') = iso_exp env lv1 ext (* Dec 2010, -fp *)
	in (ss1, A.OpExp(A.DEREF, [lv1']), ext) end
      | iso_lv env (A.Select(lv1, f2)) ext =
        (* lv1 could have large type; must isolate as an lval *)
	let val (ss1, lv1', ext1) = iso_lv env lv1 ext
	in (ss1, A.Select(lv1', f2), ext) end
      | iso_lv env (A.Marked(marked_exp)) ext =
	(* do not preserve mark, since result is statement list + pure exp *)
	iso_lv env (Mark.data marked_exp) (Mark.ext marked_exp)
      | iso_lv env e ext =
        (* any other form of expression has small type *)
	(* this case is necessary for expressions such as g()->f *)
	let val (ss, p) = iso_exp env e ext
	in (ss, p, ext) end
    
    (* iso_stm env s = ss' where the effect of s is the same
     * as executing ss'.  Declarations d are turned into statements
     * A.StmDecl(d') so that we can easily mix declarations and
     * ordinary statements and initalize temporary variables
     * at the point they are declared *)
    fun iso_stm env (A.Assign(oper_opt, lv, e)) ext =
	let val (ss1, lv1, ext1) = iso_lv env lv ext
	    val tp1 = Syn.syn_exp env lv
	in
	    iso_assign env oper_opt (ss1, lv1) tp1 e ext1 ext
	end
      | iso_stm env (A.Exp(e)) ext = iso_stmexp env e ext
      | iso_stm env (A.Seq(ds, ss)) ext =
	let val (ss1, env') = iso_decls env ds
	    val ss2 = iso_stms env' ss ext
	in
            (* preserve scope to avoid name clashes in the target code *)
	    ([A.Seq([], ss1 @ ss2)])
	end
      | iso_stm env (A.StmDecl(d)) ext =
	  (* StmDecl in source has empty scope at this point *)
          (* Does this case actually arise? Handling it this way
           * necessitates special-case treatment in Coin, where top-
           * level StmDecls behave differently. -rjs 8/20/2012 *)
          iso_stm env (A.Seq([d], [])) ext
      | iso_stm env (A.If(e, s1, s2)) ext =
	let val (ss, p) = iso_exp env e ext
	    val ss1 = iso_stm env s1 ext
	    val ss2 = iso_stm env s2 ext
	in
	    (ss @ [A.If(p, A.Seq([],ss1), A.Seq([],ss2))])
	end
      | iso_stm env (A.While(e1, invs, s2)) ext = (* ignore invariants here *)
	let val (ss1, p1) = iso_exp env e1 ext
	    val ss2 = iso_stm env s2 ext
            (* ss1 must be executed every time before testing the
	     * exit condition. We simplify the case where e1 has
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
      | iso_stm env (A.Continue) ext = [A.Continue]
      | iso_stm env (A.Break) ext = [A.Break]
      | iso_stm env (A.Return(SOME(e))) ext =
	let val (ss, p) = iso_exp env e ext
	in
	    (ss @ [marks (A.Return(SOME(p))) ext])
	end
      | iso_stm env (A.Return(NONE)) ext =
	  (* mark, so that code debugger does not skip it *)
	  [marks (A.Return(NONE)) ext]
      | iso_stm env (A.Assert(e1, e2s)) ext =
	let val (ss1, p1) = iso_exp env e1 ext
	    val (ss2, p2s) = iso_exps env e2s ext
	in
	    (ss1 @ ss2 @ [marks (A.Assert(p1, p2s)) ext])
	end
      | iso_stm env (A.Anno(specs)) ext = (* ignore specs here *)
	  []
      | iso_stm env (A.Markeds(marked_stm)) ext =
	(* do not preserve mark, since result is statement list *)
	iso_stm env (Mark.data marked_stm) (Mark.ext marked_stm)

    and iso_stms env nil ext = nil
      | iso_stms env (s::ss) ext =
	let val ss1 = iso_stm env s ext
	    val ss2 = iso_stms env ss ext
	in ss1 @ ss2 end

    (* iso_decls env ds = (ss', env'), where ss' has the same effect
     * as ds, and env' is the extension of env by declarations ds *)
    and iso_decls env (A.VarDecl(id, tp, NONE, ext)::ds) =
	let val (ss', env') = iso_decls (Symbol.bind env (id, tp)) ds
	in ([A.StmDecl(A.VarDecl(id, tp, NONE, ext))] @ ss', env') end
      | iso_decls env (A.VarDecl(id, tp, SOME(e), ext)::ds) =
	let val (ss1, p1) = iso_exp env e ext
	    val (ss2, env') = iso_decls (Symbol.bind env (id, tp)) ds
	in (ss1 @ [A.StmDecl(A.VarDecl(id, tp, SOME(p1), ext))] @ ss2,
	    env')
	end
      | iso_decls env nil = (nil, env)

    (* isolating a top-level function call is special
     * because if it has return type void we cannot bind
     * a temporary variable to its value *)
    and iso_stmexp env (A.FunCall(g, es)) ext =
	let val (ss, ps) = iso_exps env es ext
	in (ss @ [marks (A.Exp(A.FunCall(g, ps))) ext]) end
      | iso_stmexp env (A.Marked(marked_exp)) ext =
	(* do not preserve mark, since result is statement list *)
	iso_stmexp env (Mark.data marked_exp) (Mark.ext marked_exp)
      | iso_stmexp env e ext =
	let val (ss, p) = iso_exp env e ext
	in (ss @ [marks (A.Exp(p)) ext]) end
    
    (* iso_assign env oper_opt (ss1, lv1) tp1 e2 ext1 ext = ss
     * where ss has the same effect as ss1 ; lv1 = e2.
     * We assume env, decls(ss1) |- lv1 : tp1 and env |- e2 : tp1.
     * The difficult part is to guarantee left-to-right evaluation
     * of an assignment, because in A[e1] = e2, e1 must be evaluated
     * before e2, but C does not guarantee this.  Also, the out-of-bounds
     * check for A[e1] should happen before the evaluation of e2.
     * In this example, we start with A[e1] ~> ss1 ; lv1
     * and then name a pointer to the address of lv1:
     * tp1* t = &(lv1); ss2; *t = p2; where e2 ~> ss2 ; p2
     *
     * ext1 is the extent of lv1, ext the extend of the assignment itself
     *)
    and iso_assign env (oper_opt as (SOME _)) (ss1, lv1) tp1 e2 ext1 ext =
	(* compound assignment lv1 <op>= e2 ok, since lv1 pure *)
	let
	    val (ss2, p2) = iso_exp env e2 ext
	in
	    (ss1 @ ss2 @ [marks (A.Assign(oper_opt, lv1, p2)) ext])
	end
      | iso_assign env (NONE) (ss1, lv1 as A.Var _) tp1 e2 ext1 ext =
	(* x = e2 ok, since x has no effect *)
	let
	    val (ss2, p2) = iso_exp env e2 ext
	in
	    (ss1 @ ss2 @ [marks (A.Assign(NONE, lv1, p2)) ext])
	end
      | iso_assign env (NONE) (ss1, lv1 as A.OpExp(A.DEREF, _)) tp1 e2 ext1 ext =
	(* *lv1' = e2 ok, since lv1' has no effect, and *lv1 is not computed
         * as a lvalue *)
        let
	    val (ss2, p2) = iso_exp env e2 ext
	in
	    (ss1 @ ss2 @ [marks (A.Assign(NONE, lv1, p2)) ext])
	end
      | iso_assign env (NONE) (ss1, lv1) tp1 e2 ext1 ext =
	 (* lv1 = A[p1] or lv1 = lv1'.f requires transformation to guarantee
          * left-to-right.  Complication is that lv1' may have large type.
	  *)
	let
            (* use tp1, because type of e1 may be void* if NULL *)
	    val (d, t) = Syn.new_tmp (A.Pointer(tp1)) ext
	    val (ss2, p2) = iso_exp env e2 ext
	in
	    (ss1 @ [A.StmDecl(d)]		 (* ss1 ; tp1* t; *)
	     @ [marks (A.Assign(SOME(A.DEREF), t, lv1)) ext1] (* t <*>= lv1; meaning t = &lv1; *)
	     @ ss2 @ [marks (A.Assign(NONE, A.OpExp(A.DEREF, [t]), p2)) ext]) (* ss2 ; *t = p2; *)
	end

(*  fun iso_top env (A.StmDecl(d)::ss) =
	let val (ss1, env') = iso_decls env [d]
	    val ss2 = iso_top env' ss
	in ss1 @ ss2 end
      | iso_top env (A.Markeds(marked_stm)::ss) =
	  iso_top env ((Mark.data marked_stm)::ss)
      | iso_top env (s::ss) =
	let val ss1 = iso_stm env s NONE (* currently, no ext available *)
	    val ss2 = iso_top env ss
	in ss1 @ ss2 end
      | iso_top env nil = nil *)

    val iso_exp = fn env => fn e => iso_exp env e NONE (* no ext available *)
    val iso_stm = fn env => fn s => iso_stm env s NONE (* no ext available *)

end