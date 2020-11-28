(* C0 Compiler
 * Transforming contracts into explicit dynamic checks.
 * Applied if cc0 or coin are called with -d.
 *)

signature DYN_CHECK =
sig
    (* Turn contracts into dynamic checks with A.Assert(...) *)
    val contracts : Ast.program -> Ast.program
    val contracts_interpreter : Ast.tp Symbol.table -> Ast.stm -> Ast.stm
    val dummy_definitions : Symbol.symbol list -> Ast.gdecl list
end

structure Coerciontab = Symtab (type entrytp = unit)

structure DynCheck :> DYN_CHECK =
struct
    structure A = Ast

    fun location (NONE) = "_"
      | location (SOME(mark)) = Mark.show(mark)

    fun location_with_name ext g = 
        String.concat [Symbol.name g, " (", location ext, ")"]

    fun fun_type g = case Symtab.lookup g of
        SOME(A.Function(_, rtp, params, _, _, _, _)) => A.FunType(rtp, params)

    (* implementing \result in postconditions @ensures *)
    (* Aug 18, 2014 Using Symbol.new below created problems with syn_exp *)
    (* Will problems be created if user code uses variable called _result? *)
    val result_id = Symbol.new "_result" (* create new internal name *)
    val result_var = A.Var(result_id)

    (* implementing caller blame assignment in @requires
     * caller_var is added as an additional argument of type string
     * to all functions, and used in generated asserts *)
    val caller_id = Symbol.new "_caller" (* create new internal name *)
    val caller_var = A.Var(caller_id)
    val caller_decl = A.VarDecl(caller_id, A.String, NONE, NONE)
    val caller_decl_main = 
        A.VarDecl(caller_id, A.String, SOME (A.StringConst "(program start)"), NONE)

    (* tfm_test env e = e'
     * Assumes env |- e : tp for some tp
     * Ensures env, _result:rtp |- t' : tp
     * Eliminates \result, keep \length(e), \hastag(tp,e)
     * \result ~~> _result
     *)
    fun tfm_test env (e as A.Var _) = e
      | tfm_test env (e as A.IntConst _) = e
      | tfm_test env (e as A.StringConst _) = e
      | tfm_test env (e as A.CharConst _) = e
      | tfm_test env (e as A.True) = e
      | tfm_test env (e as A.False) = e
      | tfm_test env (e as A.Null) = e
      | tfm_test env (A.OpExp(oper, es)) =
        A.OpExp(oper, List.map (fn e => tfm_test env e) es)
      | tfm_test env (A.Select(e,f)) =
        A.Select(tfm_test env e, f)
      | tfm_test env (A.FunCall(g, es)) =
        A.FunCall(g, List.map (fn e => tfm_test env e) es)
      | tfm_test env (e as A.AddrOf(g)) = e
      | tfm_test env (A.Invoke(e, es)) =
        A.Invoke(tfm_test env e, List.map (fn e => tfm_test env e) es)
      | tfm_test env (e as A.Alloc(tp)) = e
      | tfm_test env (A.AllocArray(tp,e)) =
        A.AllocArray(tp, tfm_test env e)
      | tfm_test env (A.Cast(tp,e)) =
        A.Cast(tp, tfm_test env e)
      | tfm_test env (A.Result) = result_var
      | tfm_test env (A.Length(e)) =
        A.Length(tfm_test env e)
      | tfm_test env (A.Hastag(tp, e)) =
        A.Hastag(tp, tfm_test env e)
      | tfm_test env (A.Marked(marked_exp)) =
        let 
            val e' = tfm_test env (Mark.data marked_exp)
        in
            A.Marked(Mark.mark'(e', Mark.ext marked_exp))
        end

    fun m_assert(e, msg, ext) =
        A.Markeds(Mark.mark'(A.Assert(e, msg), ext))

    (* spec_to_assert env spec = A.Assert(e, msgs), marked with a region,
     * where msgs is a list of exps that constitute the error message *)
    fun spec_to_assert env (A.Requires(e,ext)) =
        let val e' = tfm_test env e
        in m_assert(e', [A.StringConst(location ext ^ ": @requires annotation failed\n"),
                                  caller_var, A.StringConst(": caller location")],
                    ext)
        end
      | spec_to_assert env (A.Ensures(e,ext)) =
        let val e' = tfm_test env e
        in m_assert(e', [A.StringConst(location ext ^ ": @ensures annotation failed")], ext) end
      | spec_to_assert env (A.LoopInvariant(e,ext)) =
        let val e' = tfm_test env e
        in m_assert(e', [A.StringConst(location ext ^ ": @loop_invariant annotation failed")], ext) end
      | spec_to_assert env (A.Assertion(e,ext)) =
        let val e' = tfm_test env e
        in m_assert(e', [A.StringConst(location ext ^ ": @assert annotation failed")], ext) end

    (* specs_to_assert env specs, see spec_to_assert *)
    fun specs_to_assert env (spec::specs) =
        let val as1 = spec_to_assert env spec
            val ass2 = specs_to_assert env specs
        in as1::ass2 end
      | specs_to_assert env nil = nil

    (* anno_to_assert env anno = ass, see spec to assert.
     * This is only called on explicit @assert or @loop_invariant *)
    fun anno_to_assert env (A.Anno(specs)) =
        List.map (fn spec => spec_to_assert env spec) specs

    (* dc_stm env s post = s'
     * Assumes env |- s stmt and env0, _result : rtp |- post stmt
     * post is function postcondition, formulated as asserts
     *)
    fun dc_stm env (s as A.Assign _) post = s
      | dc_stm env (s as A.Exp _) post = s
      | dc_stm env (A.Seq(ds, ss)) post =
        let val env' = Syn.syn_decls env ds
        in 
          A.Seq(ds, List.map (fn s => dc_stm env' s post) ss)
        end 
      | dc_stm env (s as A.StmDecl d) post = s 
      | dc_stm env (A.If(e, s1, s2)) post =
          A.If(e, dc_stm env s1 post, dc_stm env s2 post)
      | dc_stm env (A.While(e, invs, s)) post =
        let val ass = specs_to_assert env invs
        (* ass is loop invariant in the form of assert statements *)
        in
          A.While(A.True, nil, (* eliminate invariants here, correct? *)
                  A.Seq(nil, ass @ [A.If(e, dc_stm env s post, A.Break)]))
        end
      (* A.For should be impossible *)
      | dc_stm env (A.Continue) post = A.Continue
      | dc_stm env (A.Break) post = A.Break
      | dc_stm env (A.Return(SOME(e))) post =
          A.Seq(nil, [A.Assign(NONE,result_var,e)]
                     @ post
                     @ [A.Return(SOME(result_var))])
      | dc_stm env (A.Return(NONE)) post =
          A.Seq(nil, post @ [A.Return(NONE)])
      | dc_stm env (s as A.Assert _) post = s
      | dc_stm env (s as A.Error _) post = s
      | dc_stm env (A.Anno(specs)) post =
        let val ass = specs_to_assert env specs
        in
            A.Seq(nil, ass)
        end 
      | dc_stm env (A.Markeds(marked_stm)) post =
          A.Markeds(Mark.mark'(dc_stm env (Mark.data marked_stm) post,
                               Mark.ext marked_stm))
    and dc_stms env ss post =
          List.map (fn s => dc_stm env s post) ss

    fun extract_pre env ((spec as A.Requires _)::specs) =
        let val as1 = spec_to_assert env spec
            val ass2 = extract_pre env specs
        in as1 :: ass2 end
      | extract_pre env (_::specs) = extract_pre env specs
      | extract_pre env nil = nil

    fun extract_post env ((spec as A.Ensures _)::specs) =
        let val as1 = spec_to_assert env spec
            val ass2 = extract_post env specs
        in as1 :: ass2 end
      | extract_post env (_::specs) = extract_post env specs
      | extract_post env nil = nil

    fun is_main_fn g = EQUAL = Symbol.compare (g, Symbol.symbol "main")

    fun is_external_fun g =
        ( case Symtab.lookup g
           of SOME(A.Function(g', rtp, params, bodyOpt, specs, is_extern, ext)) => is_extern
            | _ => false )

    (* fv_stm and fv_exp redirect function calls to the instance
     * of a function currently in effect, according to the table
     * Funversiontab.  Call this after annotations are turned
     * into asserts.
     * This handles multiple declarations of a function, each with
     * contracts.
     *)
    fun fv_exp (e as A.Var _) ext g = e
      | fv_exp (e as A.IntConst _) ext g = e
      | fv_exp (e as A.StringConst _) ext g = e
      | fv_exp (e as A.CharConst _) ext g = e
      | fv_exp (e as A.True) ext g = e
      | fv_exp (e as A.False) ext g = e
      | fv_exp (e as A.Null) ext g = e
      | fv_exp (A.OpExp(oper,es)) ext g =
          A.OpExp(oper, List.map (fn e => fv_exp e ext g) es)
      | fv_exp (A.Select(e, f)) ext g =
          A.Select(fv_exp e ext g, f)
      | fv_exp (A.FunCall(g, es)) ext callerName =
        let val es' = List.map (fn e => fv_exp e ext callerName) es
            val (g_last, i_last, is_extern) =
                case Funversiontab.lookup g
                 of NONE => (g, 0, is_external_fun g)
                  | SOME(g_i, i) => (g_i, i, false) (* versioned functions are not external *)
        in
            (* if g is not an external function, we add the caller
             * location in the form of a string as an additional argument *)
            A.FunCall(g_last, if is_extern orelse is_main_fn g_last
                              then es'
                              else es' @ [A.StringConst(location_with_name ext callerName)])
        end
      | fv_exp (A.AddrOf(g)) ext callerName =
        let val (g_last, i_last, is_extern) =
                case Funversiontab.lookup g
                 of NONE => (g, 0, is_external_fun g)
                  | SOME(g_i, i) => (g_i, i, false) (* versioned functions are not external *)
        in A.AddrOf(g_last) end
      | fv_exp (A.Invoke(e, es)) ext g =
        let val (e'::es') = List.map (fn e => fv_exp e ext g) (e::es)
        (* external functions are wrapped; 'main' cannot be invoked *)
        in A.Invoke(e', es' @ [A.StringConst(location_with_name ext g)]) end 
      | fv_exp (e as A.Alloc _) ext g = e
      | fv_exp (A.AllocArray(t, e)) ext g =
          A.AllocArray(t, fv_exp e ext g)
      | fv_exp (A.Cast(t, e)) ext g =
          A.Cast(t, fv_exp e ext g)
      | fv_exp (e as A.Result) ext g = e
      | fv_exp (A.Length(e)) ext g =
          A.Length(fv_exp e ext g)
      | fv_exp (A.Hastag(tp, e)) ext g =
          A.Hastag(tp, fv_exp e ext g)
      (* A.Old should be impossible *)
      | fv_exp (A.Marked(marked_exp)) ext g =
          A.Marked(Mark.mark'(fv_exp (Mark.data marked_exp) (Mark.ext marked_exp) g,
                              Mark.ext marked_exp))

    (* fv_stm s ext = s', translating functions calls in
     * to add source location argument.  Contracts have already
     * been translated away. *)
    fun fv_stm (A.Assign(oper_opt, lv, e)) ext g =
          A.Assign(oper_opt, fv_exp lv ext g, fv_exp e ext g)
      | fv_stm (A.Exp(e)) ext g = A.Exp(fv_exp e ext g)
      | fv_stm (A.Seq(ds, ss)) ext g = 
          A.Seq(List.map (fn d => fv_decl d g) ds,
                List.map (fn d => fv_stm d ext g) ss)
      | fv_stm (A.StmDecl d) ext g = A.StmDecl (fv_decl d g)
      | fv_stm (A.If(e, s1, s2)) ext g =
          A.If(fv_exp e ext g, fv_stm s1 ext g, fv_stm s2 ext g)
      | fv_stm (A.While(e, invs, s)) ext g = (* ignore invs *)
          A.While(fv_exp e ext g, invs, fv_stm s ext g)
      (* A.For should be impossible *)
      | fv_stm (s as A.Continue) ext g = s
      | fv_stm (s as A.Break) ext g = s
      | fv_stm (s as A.Return(NONE)) ext g = 
          A.Seq([], [s])
      | fv_stm (A.Return(SOME(e))) ext g =
          A.Seq([], [A.Return(SOME(fv_exp e ext g))])
      | fv_stm (A.Assert(e1, e2s)) ext g =
          A.Assert(fv_exp e1 ext g, List.map (fn e => fv_exp e ext g) e2s)
      | fv_stm (A.Error e) ext g = 
          A.Error(fv_exp e ext g)
      (* A.Anno should be impossible *)
      | fv_stm (A.Markeds(marked_stm)) ext g =
          A.Markeds(Mark.mark'(fv_stm (Mark.data marked_stm) (Mark.ext marked_stm) g,
                               Mark.ext marked_stm))

    and fv_decl (d as A.VarDecl(x, t, NONE, ext)) g = d
      | fv_decl (A.VarDecl(x, t, SOME(e), ext)) g =
          A.VarDecl(x, t, SOME(fv_exp e ext g), ext)

    fun param_to_arg (A.VarDecl(x, t, NONE, ext)) = A.Var(x)

    (* creates a new wrapper, calling original symbol g *)
    (* to fix: wrapper should pass caller_id through !!! -fp *)
    fun fun_wrapper (A.Function(g, A.Void, params, NONE, specs, is_external, ext)) g_next =
        (* return type is A.Void *)
        let val args = List.map param_to_arg params
            val body = A.Seq([], [A.Exp(A.FunCall(g, args)), A.Return(NONE)])
            (* wrapper is never external; therefore 'false' below *)
            val gdecl = A.Function(g_next, A.Void, params, SOME(body), specs, false, ext)
        in
            gdecl
        end
      | fun_wrapper (A.Function(g, rtp, params, NONE, specs, is_external, ext)) g_next =
        (* rtp <> A.Void *)
        let val args = List.map param_to_arg params
            val body = A.Seq([], [A.Return(SOME(A.FunCall(g, args)))])
            (* wrapper is never external; therefore 'false' below *)
            val gdecl = A.Function(g_next, rtp, params, SOME(body), specs, false, ext)
        in
            gdecl
        end

    (* coercion_wrapper g funtp g' = gdecl
     * where gdecl defines g' to call g and add specs from funtp *)
    fun coercion_wrapper g (A.FunTypeDef(fid, rtp, params, specs, ext)) g' =
        let val args = List.map param_to_arg params
            val body = case rtp
                        of A.Void => A.Seq([], [A.Exp(A.FunCall(g, args)), A.Return(NONE)])
                         | _ => A.Seq([], [A.Return(SOME(A.FunCall(g, args)))])
            (* wrapper is never external; therefore 'false' below *)
            val gdecl = A.Function(g', rtp, params, SOME(body), specs, false, ext)
        in
            gdecl
        end

    (* contracts_interpreter env stm = stm'
     * called by coin *)
    fun contracts_interpreter env stm = 
        let val stm' = dc_stm env stm nil
            val stm'' = fv_stm stm' NONE (Symbol.new "(coin top level)")
        in 
            stm'' 
        end

    (* tfm_fundef fundef = fundef'
     * Translate contracts into appropriate asserts *)
    fun tfm_fundef (A.Function(g, rtp, params, SOME(body), specs, is_external, ext)) =
        let val dresult = case rtp
                           of A.Void => []
                            | _ => [A.VarDecl (result_id, rtp, NONE, ext)]
            (* params1 has caller_id as additional string argument *)
            val (params1, ds0) = if is_main_fn g
                          then (params, [caller_decl_main]) 
                          else (params @ [caller_decl], [])
            val env0 = Syn.syn_decls Symbol.empty params1
            val env1 = Symbol.bind env0 (result_id, rtp) (* replaced "\\result" -fp *)
            val ass1 = extract_pre env1 specs
            val ass2 = extract_post env1 specs
            (* ass2 = postcondition; insert before return *)
            val body' = dc_stm env1 body ass2
            
            (* add possibly redundant (dead-code) post-condition *)
            (* to make sure it is checked in case there is no return in body s *)
            val body'' = case rtp
                         of A.Void => A.Seq(ds0 @ dresult,
                                            ass1 @ [body'] @ ass2)
                          | _ => A.Seq(ds0 @ dresult, 
                                       ass1 @ [body'])
            val body''' = fv_stm body'' ext g 
        in
            A.Function(g, rtp, params1, SOME(body'''), specs, is_external, ext)
        end

    (* defining and insertion coercions at function pointer types *)
    (* should this use internal names?  Aug 19, 2014 -fp *)
    fun coercion_name g fid =
        Symbol.nsymbol Symbol.Internal (Symbol.name g ^ "__" ^ Symbol.name fid)

    (* elaborate non-trivial coercions *)
    fun ec_exp env (e as A.Var _) = e
      | ec_exp env (e as A.IntConst _) = e
      | ec_exp env (e as A.StringConst _) = e
      | ec_exp env (e as A.CharConst _) = e
      | ec_exp env (e as A.True) = e
      | ec_exp env (e as A.False) = e
      | ec_exp env (e as A.Null) = e
      | ec_exp env (e as A.OpExp(A.COND, [e1,e2,e3])) =
        let val e1' = ec_exp env e1
            val tp' = Syn.syn_exp env e (* type of the whole conditional *)
            val e2' = ec_exp env e2
            val e2'' = coerce_exp env e2' tp'
            val e3' = ec_exp env e3
            val e3'' = coerce_exp env e3' tp'
        in A.OpExp(A.COND, [e1', e2'', e3'']) end
      | ec_exp env (A.OpExp(opr, es)) =
          A.OpExp(opr, List.map (fn e => ec_exp env e) es)
      | ec_exp env (A.Select(e, f)) =
          A.Select(ec_exp env e, f)
      | ec_exp env (A.FunCall(g, es)) =
        let val A.FunType(rtp, params) = fun_type g
            val es' = List.map (fn e => ec_exp env e) es
            val es'' = coerce_exps env es' (List.map (fn A.VarDecl(_,tp',_,_) => tp') params)
        in
            A.FunCall(g, es'')
        end
      | ec_exp env (e as A.AddrOf(g)) = e
      | ec_exp env (A.Invoke(e, es)) =
        let val e' = ec_exp env e
            val A.FunType(rtp, params) = Syn.expand_fdef (Syn.syn_exp env e)
            val es' = List.map (fn e => ec_exp env e) es
            val es'' = coerce_exps env es' (List.map (fn A.VarDecl(_,tp',_,_) => tp') params)
        in
            A.Invoke(e', es'')
        end
      | ec_exp env (e as A.Alloc _) = e
      | ec_exp env (A.AllocArray(tp, e)) = A.AllocArray(tp, ec_exp env e)
      | ec_exp env (A.Cast(tp, e)) = (* Aug 17, 2014 should this be a possible coercion site? -fp *)
          A.Cast(tp, ec_exp env e)
      | ec_exp env (e as A.Result) = e
      | ec_exp env (A.Length(e)) = A.Length(ec_exp env e)
      | ec_exp env (A.Hastag(tp,e)) = A.Hastag(tp, ec_exp env e)
      | ec_exp env (A.Marked(marked_exp)) =
        let val e' = ec_exp env (Mark.data marked_exp)
        in A.Marked(Mark.mark'(e', Mark.ext marked_exp)) end

    and coerce_exp env e tp' =
        let val tp = Syn.syn_exp env e
        in
            if TypeChecker.tp_equal tp tp' (* function type names are nominal here *)
            then e                         (* identity coercion *)
            else coerce2_exp env e (Syn.expand_all tp) (Syn.expand_all tp')
        end

    and coerce_exps env nil nil = nil
      | coerce_exps env (e::es) (tp::tps) =
        coerce_exp env e tp::coerce_exps env es tps

    (* coerce2_exp env e tp tp' = e', requires e : tp, ensures e' : tp' *)
    and coerce2_exp env (A.OpExp(A.COND, [e1, e2, e3])) tp tp' =
        let val e2' = coerce2_exp env e2 tp tp'
            val e3' = coerce2_exp env e3 tp tp'
        in A.OpExp(A.COND, [e1, e2', e3']) end
      | coerce2_exp env (A.Marked(marked_exp)) tp tp' =
        let val e' = coerce2_exp env (Mark.data marked_exp) tp tp'
        in A.Marked(Mark.mark'(e', Mark.ext marked_exp)) end
      | coerce2_exp env (e as A.AddrOf(g)) (A.Pointer(A.FunType(rtp, params))) (A.Pointer(A.FunTypeName(fid))) =
        ( case Symtab.lookup fid
           of SOME(A.FunTypeDef(fid', rtp', params', nil, ext)) =>
              (* no additional specs; do not coerce *)
              e
            | SOME(ftpdef as A.FunTypeDef(fid', rtp', params', specs', ext)) =>
              (* specs' <> nil *)
              let val g' = coercion_name g fid
              (* 
                  val () = TextIO.print("% Coercing function '" ^ Symbol.name g ^ "' to type '" ^ Symbol.name fid ^ "'\n")
               *)
              in
                  case Symtab.lookup g'
                   of SOME(A.Function _) => A.AddrOf(g')  (* already needed the same coercion *)
                    | NONE => let val d' = coercion_wrapper g ftpdef g'
                                  val d'' = tfm_fundef d' (* translate contracts into asserts *)
                                  val () = Symtab.bind(g', d'') (* enter into symbol table *)
                                  val () = Coerciontab.bind(g', ()) (* newly defined coercion *)
                              in
                                  A.AddrOf(g')
                              end
              end
        )
      | coerce2_exp env e tp tp' =
        (* must come from NULL : any* <: t* *)
        (* coercion is the identity *)
        e

    (* ec_stm env s rtp = s', where rtp is the return type
     * of the function we are in the body of
     *)
    fun ec_stm env (A.Assign(NONE, lv, e)) rtp =
        let val lv' = ec_exp env lv
            val e' = ec_exp env e
            val tp' = Syn.syn_exp env lv
            val e'' = coerce_exp env e' tp'
        in A.Assign(NONE, lv', e'') end
      | ec_stm env (A.Assign(SOME(opr), lv, e)) rtp =
        (* compound assignments, all on type int *)
        A.Assign(SOME(opr), ec_exp env lv, ec_exp env e)
      | ec_stm env (A.Exp(e)) rtp = A.Exp(ec_exp env e)
      | ec_stm env (A.Return(SOME(e))) rtp =
        A.Return(SOME(coerce_exp env e rtp))
      | ec_stm env (s as A.Return(NONE)) rtp = s
      | ec_stm env (A.Assert(e1, e2s)) rtp =
        A.Assert(ec_exp env e1, e2s)
      | ec_stm env (A.Error(e)) rtp =
        A.Error(ec_exp env e)
      | ec_stm env (A.Anno(specs)) rtp =
        A.Anno(List.map (fn spec => ec_spec env spec) specs)
      | ec_stm env (A.Seq(ds,ss)) rtp =
        let val (env', ds') = ec_decls env ds nil
        in A.Seq(ds', List.map (fn s => ec_stm env' s rtp) ss) end
      | ec_stm env (A.StmDecl(d)) rtp = (* used where? *)
        let val (env', [d']) = ec_decls env [d] nil (* ignore env'? *)
        in A.StmDecl(d') end
      | ec_stm env (A.If(e, s1, s2)) rtp =
        A.If(ec_exp env e, ec_stm env s1 rtp,
                           ec_stm env s2 rtp)
      | ec_stm env (A.While(e, invs, s)) rtp =
        A.While(ec_exp env e, List.map (fn spec => ec_spec env spec) invs,
                ec_stm env s rtp)
      | ec_stm env (s as A.Continue) rtp = s
      | ec_stm env (s as A.Break) rtp = s
      | ec_stm env (A.Markeds(marked_stm)) rtp =
        let val s' = ec_stm env (Mark.data marked_stm) rtp
        in A.Markeds(Mark.mark'(s', Mark.ext marked_stm)) end
      (* A.For should be impossible *)

    and ec_decls env nil ds' = (env, List.rev ds')
      | ec_decls env ((d as A.VarDecl(id, tp, NONE, ext))::ds) ds' =
          ec_decls (Symbol.bind env (id, tp)) ds (d::ds')
      | ec_decls env (A.VarDecl(id, tp, SOME(e), ext)::ds) ds' =
        let val e' = ec_exp env e
            val e'' = coerce_exp env e' tp
            val d' = A.VarDecl(id, tp, SOME(e''), ext)
        in
            ec_decls (Symbol.bind env (id, tp)) ds (d'::ds')
        end

    and ec_spec env (A.Requires(e, ext)) = A.Requires(ec_exp env e, ext)
      | ec_spec env (A.Ensures(e, ext)) = A.Ensures(ec_exp env (tfm_test env e), ext) (* elim \result *)
      | ec_spec env (A.LoopInvariant(e, ext)) = A.LoopInvariant(ec_exp env e, ext)
      | ec_spec env (A.Assertion(e, ext)) = A.Assertion(ec_exp env e, ext)

    fun next_name (fun_name, fun_index) =
        (* create new internal function version name *)
        let
            val g = Symbol.new (fun_name ^ "__" ^ Int.toString fun_index)
        in
            case Symtab.lookup(g)
             of NONE => (g, fun_index)
              | SOME _ => next_name (fun_name, fun_index+1)
        end

    fun elab_coercions (A.Function(g, rtp, params, SOME(s), specs, is_external, ext)) =
        let val env0 = Syn.syn_decls Symbol.empty params
            val env1 = Symbol.bind env0 (result_id, rtp)
            val specs' = List.map (fn spec => ec_spec env1 spec) specs
            val s' = ec_stm env1 s rtp
        in
            A.Function(g, rtp, params, SOME(s'), specs', is_external, ext)
        end
      | elab_coercions d = d

    (* dc_gdecl gdecl = gdecls' transforms global declaration to add
     * function versioning and turn contract annotations into asserts.
     * Sometimes we need to split a declaration in two *)
    fun dc_gdecl (d as A.Function(g, rtp, params, SOME(s), specs, is_external, ext)) =
        (* Symbol instance remains the same for definition; no new function environment *)
        (* Add caller id argument to function *)
        let val () = Coerciontab.reset() (* track new coercion functions *)
            val d' = elab_coercions d    (* now Coerciontab has new function symbols, if any *)
            val d'' = tfm_fundef d'
            (* don't replace old definition so elab_coercions
             * still sees the old types, which are correct for
             * function definitions that have not yet been transformed *)
            (* val () = Symtab.bind(g, d'') *)
            val ds = List.map (fn g => Option.valOf (Symtab.lookup g)) (Coerciontab.list ())
        (* coercions have already be transformed when entered into symbol table *)
        in (* coercion function ds come before use in d'' *)
            ds @ [d'']
        end
      | dc_gdecl (d as A.Function(g, rtp, params, NONE, nil, true, ext)) =
        (* external function declaration remains identical, if no contracts *)
        [d]
      | dc_gdecl (d as A.Function(g, rtp, params, NONE, nil, false, ext)) =
        (* no specifications (specs = nil); transform to add argument *)
        [A.Function(g, rtp, params @ [caller_decl], NONE, nil, false, ext)]
      | dc_gdecl (d as A.Function(g, rtp, params, NONE, specs as (_::_), is_external, ext)) =
        (* specifications (function prototype with contracts but no body); create new wrapper for g *)
        let 
            val g_opt = Funversiontab.lookup g
            val (g_last, i_last) = case g_opt of NONE => (g,0) | SOME(g_i,i) => (g_i,i)
            val (g_next, i_next) = next_name (Symbol.name g, i_last+1)
            val d' = fun_wrapper d g_next
            val d'' = tfm_fundef d' (* embedded calls go to last version! *)
            (* enter in symbol table so Syn.syn works on transformed program
             * however, the transformed program is not well-typed according to
             * the symbol table, since other functions retain their old types
             * (see case for function definitions above)
             * if this becomes an issue, a second pass over the symbol table
             * may be necessary to restore typing invariants *)
            val _ = Symtab.bind(g_next, d'')
            val _ = Funversiontab.bind(g, (g_next, i_next)) (* bind latest version *)
            (* add caller id argument to forward declaration *)
            val d1 = if is_external
                     then d
                     else A.Function(g, rtp, params @ [caller_decl], NONE, specs, is_external, ext)
            (* we cannot tell here if it will never be used, since multiple
             * files are transformed in sequence
             *)
            (*
            val d1' = if is_never_defined g
                      then dummy_definition d1
                      else d1
             *)
        in
            (* preserve first decl, if present, as forward declaration *)
            (* or add in dummy definition if never defined *)
            case g_opt of NONE => [d1,d''] | SOME _ => [d'']
        end
      | dc_gdecl (A.FunTypeDef(fid, rtp, params, specs, ext)) =
        (* specs are transformed wherever this function type definition
         * is used as a coercion
         * should we keep or replace the old definition? *)
        [A.FunTypeDef(fid, rtp, params @ [caller_decl], specs, ext)]
      (* struct and type definitions *)
      | dc_gdecl d = [d]

   fun dc_gdecls nil = nil
     | dc_gdecls (gdecl::gdecls) =
         dc_gdecl gdecl @ dc_gdecls gdecls

   fun contracts gdecls = dc_gdecls gdecls

   (* dummy_def relies on the symbol table retaining the original declaration *)
   fun dummy_def (SOME(A.Function(g, rtp, params, NONE, specs, false, ext))) =
       (* only apply to non-external functions (false), with no definition (NONE) *)
       let val body = A.Error(A.StringConst("function '" ^ Symbol.name g ^ "' declared but never defined"))
       in
           A.Function(g, rtp, params @ [caller_decl], SOME(A.Seq([], [body])), specs, false, ext)
       end
       (* all other cases should be impossible *)
   fun dummy_definitions gs = List.map (dummy_def o Symtab.lookup) gs

end
