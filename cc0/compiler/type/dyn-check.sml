(* C0 Compiler
 * Transforming contracts into explicit dynamic checks.
 * Applied if cc0 or coin are called with -d.
 *)

signature DYN_CHECK =
sig
    (* Turn contracts into dynamic checks with A.Assert(...) *)
    val contracts : Ast.program -> Ast.program
    val contracts_interpreter : Ast.tp Symbol.table -> Ast.stm -> Ast.stm
end

structure DynCheck :> DYN_CHECK =
struct
    structure A = Ast

    fun location (NONE) = "_"
      | location (SOME(mark)) = Mark.show(mark)

    (* implementing \result in postconditions @ensures *)
    val result_id = Symbol.new "_result" (* create new internal name *)
    val result_var = A.Var(result_id)

    (* implementing caller blame assignment in @requires
     * caller_var is added as an additional argument of type string
     * to all functions, and used in generated asserts *)
    val caller_id = Symbol.new "_caller" (* create new internal name *)
    val caller_var = A.Var(caller_id)
    val caller_decl = A.VarDecl(caller_id, A.String, NONE, NONE)
    val caller_decl_main = 
        A.VarDecl(caller_id, A.String, SOME (A.StringConst "(none)"), NONE)

    (* tfm_test env e = (ds, ss, e')
     * Assumes env |- e : tp for some tp
     * Ensures env, ds |- ss stm and env, ds |- e' : tp
     * Eliminates \result, keep \length(e), \hastag(tp,e)
     * \result ~~> _result
     *)
    fun tfm_test env (e as A.Var _) = ([],[],e)
      | tfm_test env (e as A.IntConst _) = ([],[],e)
      | tfm_test env (e as A.StringConst _) = ([],[],e)
      | tfm_test env (e as A.CharConst _) = ([],[],e)
      | tfm_test env (e as A.True) = ([],[],e)
      | tfm_test env (e as A.False) = ([],[],e)
      | tfm_test env (e as A.Null) = ([],[],e)
      | tfm_test env (A.OpExp(oper, es)) =
	let val (ds, ss, es') = tfm_tests env es
	in (ds, ss, A.OpExp(oper, es')) end
      | tfm_test env (A.Select(e,f)) =
	let val (ds, ss, e') = tfm_test env e
	in (ds, ss, A.Select(e',f)) end
      | tfm_test env (A.FunCall(g, es)) =
	let val (ds, ss, es') = tfm_tests env es
	in (ds, ss, A.FunCall(g, es')) end
      | tfm_test env (e as A.Alloc(tp)) = ([],[],e)
      | tfm_test env (A.AllocArray(tp,e)) =
	let val (ds, ss, e') = tfm_test env e
         in (ds, ss, A.AllocArray(tp, e')) end
      | tfm_test env (A.Cast(tp,e)) =
        let val (ds, ss, e') = tfm_test env e
        in (ds, ss, A.Cast(tp, e')) end
      | tfm_test env (A.Result) = ([], [], result_var)
      | tfm_test env (A.Length(e)) =
	let val (ds, ss, e') = tfm_test env e
	in (ds, ss, A.Length(e')) end
      | tfm_test env (A.Hastag(tp, e)) =
        let val (ds, ss, e') = tfm_test env e
        in (ds, ss, A.Hastag(tp, e')) end
      (* 
      | tfm_test env (A.Old(e)) =
	let val (d,t) = Syn.new_tmp (Syn.syn_exp env e) NONE (* fix NONE? -fp *)
	    val (ds, ss, e') = tfm_test env e
	(* \old cannot be nested; transform anyway for \result *)
	in (ds @ [d], ss @ [A.Assign(NONE, t, e')], t) end
      *)
      | tfm_test env (A.Marked(marked_exp)) =
	(* simple heuristic for preserving location info *)
	let 
	    val (ds, ss, e') = tfm_test env (Mark.data marked_exp)
	in
	    (ds, ss, A.Marked(Mark.mark'(e', Mark.ext marked_exp)))
	end

    (* tfm_tests env es = (ds, ss, es'), as in tfm_test *)
    and tfm_tests env (e::es) =
	let val (ds1, ss1, e') = tfm_test env e
	    val (ds2, ss2, es') = tfm_tests env es
	in (ds1 @ ds2, ss1 @ ss2, e'::es') end
      | tfm_tests env nil = ([], [], nil)

    fun m_assert(e, msg, ext) =
	A.Markeds(Mark.mark'(A.Assert(e, msg), ext))

    (* spec_to_assert env spec = A.Assert(e, msgs), marked with a region,
     * where msgs is a list of exps that constitute the error message *)
    fun spec_to_assert env (A.Requires(e,ext)) =
	let val (ds, ss, e') = tfm_test env e
	in (ds, ss, m_assert(e', [A.StringConst(location ext ^ ": @requires annotation failed\n"),
				  caller_var, A.StringConst(": caller location")],
			     ext))
	end
      | spec_to_assert env (A.Ensures(e,ext)) =
	let val (ds, ss, e') = tfm_test env e
	in (ds, ss, m_assert(e', [A.StringConst(location ext ^ ": @ensures annotation failed")], ext)) end
      | spec_to_assert env (A.LoopInvariant(e,ext)) =
	let val (ds, ss, e') = tfm_test env e
	in (ds, ss, m_assert(e', [A.StringConst(location ext ^ ": @loop_invariant annotation failed")], ext)) end
      | spec_to_assert env (A.Assertion(e,ext)) =
	let val (ds, ss, e') = tfm_test env e
	in (ds, ss, m_assert(e', [A.StringConst(location ext ^ ": @assert annotation failed")], ext)) end

    (* specs_to_assert env specs, see spec_to_assert *)
    fun specs_to_assert env (spec::specs) =
	let val (ds1, ss1, as1) = spec_to_assert env spec
	    val (ds2, ss2, ass2) = specs_to_assert env specs
	in (ds1 @ ds2, ss1 @ ss2, [as1] @ ass2) end
      | specs_to_assert env nil = ([], [], [])

    (* anno_to_assert env anno = ass, see spec to assert.
     * This is only called on explicit @assert or @loop_invariant *)
    fun anno_to_assert env (A.Anno(specs)) =
	let val (nil, nil, ass1) = specs_to_assert env specs
	(* no \old permitted in loop invariants or assert *)
	in ass1 end

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
	let val (nil, nil, ass) = specs_to_assert env invs
        (* no \old permitted in loop invariants, so ds and ss are empty *)   
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
	let val ([], [], ass) = specs_to_assert env specs
	(* no \old allowed in assertions, only postconditions *)
	in
	    A.Seq(nil, ass)
	end 
      | dc_stm env (A.Markeds(marked_stm)) post =
	  A.Markeds(Mark.mark'(dc_stm env (Mark.data marked_stm) post,
                               Mark.ext marked_stm))
    and dc_stms env ss post =
	  List.map (fn s => dc_stm env s post) ss

    fun extract_pre env ((spec as A.Requires _)::specs) =
	let val (ds1, ss1, as1) = spec_to_assert env spec
	    val (ds2, ss2, ass2) = extract_pre env specs
	in (ds1 @ ds2, ss1 @ ss2, [as1] @ ass2) end
      | extract_pre env (_::specs) = extract_pre env specs
      | extract_pre env nil = ([], [], [])

    fun extract_post env ((spec as A.Ensures _)::specs) =
	let val (ds1, ss1, as1) = spec_to_assert env spec
	    val (ds2, ss2, ass2) = extract_post env specs
	in (ds1 @ ds2, ss1 @ ss2, [as1] @ ass2) end
      | extract_post env (_::specs) = extract_post env specs
      | extract_post env nil = ([], [], [])

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
    fun fv_exp (e as A.Var _) ext = e
      | fv_exp (e as A.IntConst _) ext = e
      | fv_exp (e as A.StringConst _) ext = e
      | fv_exp (e as A.CharConst _) ext = e
      | fv_exp (e as A.True) ext = e
      | fv_exp (e as A.False) ext = e
      | fv_exp (e as A.Null) ext = e
      | fv_exp (A.OpExp(oper,es)) ext =
	  A.OpExp(oper, List.map (fn e => fv_exp e ext) es)
      | fv_exp (A.Select(e, f)) ext =
	  A.Select(fv_exp e ext, f)
      | fv_exp (A.FunCall(g, es)) ext =
	let val es' = List.map (fn e => fv_exp e ext) es
	    val (g_last, i_last, is_extern) =
		case Funversiontab.lookup g
		 of NONE => (g, 0, is_external_fun g)
		  | SOME(g_i, i) => (g_i, i, false) (* versioned functions are not external *)
	in
	    (* if g is not an external function, we add the caller
             * location in the form of a string as an additional argument *)
	    A.FunCall(g_last, if is_extern orelse is_main_fn g_last
			      then es'
			      else es' @ [A.StringConst(location(ext))])
	end 
      | fv_exp (e as A.Alloc _) ext = e
      | fv_exp (A.AllocArray(t, e)) ext =
	  A.AllocArray(t, fv_exp e ext)
      | fv_exp (A.Cast(t, e)) ext =
          A.Cast(t, fv_exp e ext)
      | fv_exp (e as A.Result) ext = e
      | fv_exp (A.Length(e)) ext =
	  A.Length(fv_exp e ext)
      | fv_exp (A.Hastag(tp, e)) ext =
          A.Hastag(tp, fv_exp e ext)
      (* A.Old should be impossible *)
      | fv_exp (A.Marked(marked_exp)) ext =
	  A.Marked(Mark.mark'(fv_exp (Mark.data marked_exp) (Mark.ext marked_exp),
			      Mark.ext marked_exp))

    (* fv_stm s ext = s', translating functions calls in
     * to add source location argument.  Contracts have already
     * been translated away. *)
    fun fv_stm (A.Assign(oper_opt, lv, e)) ext =
	  A.Assign(oper_opt, fv_exp lv ext, fv_exp e ext)
      | fv_stm (A.Exp(e)) ext = A.Exp(fv_exp e ext)
      | fv_stm (A.Seq(ds, ss)) ext = 
	  A.Seq(List.map (fn d => fv_decl d) ds,
		List.map (fn d => fv_stm d ext) ss)
      | fv_stm (A.StmDecl d) ext = A.StmDecl (fv_decl d)
      | fv_stm (A.If(e, s1, s2)) ext =
	  A.If(fv_exp e ext, fv_stm s1 ext, fv_stm s2 ext)
      | fv_stm (A.While(e, invs, s)) ext = (* ignore invs *)
	  A.While(fv_exp e ext, invs, fv_stm s ext)
      (* A.For should be impossible *)
      | fv_stm (s as A.Continue) ext = s
      | fv_stm (s as A.Break) ext = s
      | fv_stm (s as A.Return(NONE)) ext = s
      | fv_stm (A.Return(SOME(e))) ext =
	  A.Return(SOME(fv_exp e ext))
      | fv_stm (A.Assert(e1, e2s)) ext =
	  A.Assert(fv_exp e1 ext, List.map (fn e => fv_exp e ext) e2s)
      | fv_stm (A.Error e) ext = 
          A.Error(fv_exp e ext)
      (* A.Anno should be impossible *)
      | fv_stm (A.Markeds(marked_stm)) ext =
	  A.Markeds(Mark.mark'(fv_stm (Mark.data marked_stm) (Mark.ext marked_stm),
			       Mark.ext marked_stm))

    and fv_decl (d as A.VarDecl(x, t, NONE, ext)) = d
      | fv_decl (A.VarDecl(x, t, SOME(e), ext)) =
	  A.VarDecl(x, t, SOME(fv_exp e ext), ext)

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

    (* contracts_interpreter env stm = stm'
     * called by coin *)
    fun contracts_interpreter env stm = 
        let val stm' = dc_stm env stm nil
            val stm'' = fv_stm stm' NONE
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
	    (* val env1 = Symbol.bind env0 (Symbol.symbol "\\result", rtp) *)
	    val env1 = Symbol.bind env0 (result_id, rtp) (* replaced "\\result" -fp *)
	    val (ds1, ss1, ass1) = extract_pre env1 specs (* ds1 = ss1 = [] *)
	    val (ds2, ss2, ass2) = extract_post env1 specs (* ss2 = computations of \old(e) *)
            (* ass2 = postcondition; insert before return *)
	    val body' = dc_stm env1 body ass2
            (* add possibly redundant (dead-code) post-condition *)
	    (* to make sure it is checked in case there is no return in body s *)
	    val body'' = case rtp
			 of A.Void => A.Seq(ds0 @ ds1 @ ds2 @ dresult,
					    ss1 @ ss2 @ ass1 @ [body'] @ ass2)
			  | _ => A.Seq(ds0 @ ds1 @ ds2 @ dresult,
				       ss1 @ ss2 @ ass1 @ [body'])
	    val body''' = fv_stm body'' ext
	in
	    A.Function(g, rtp, params1, SOME(body'''), specs, is_external, ext)
	end

    fun next_name (fun_name, fun_index) =
        (* create new internal function version name *)
	let
            val g = Symbol.new (fun_name ^ "__" ^ Int.toString fun_index)
	in
	    case Symtab.lookup(g)
	     of NONE => (g, fun_index)
	      | SOME _ => next_name (fun_name, fun_index+1)
	end

    (* dc_gdecl gdecl = gdecls' transforms global declaration to add
     * function versioning and turn contract annotations into asserts.
     * Sometimes we need to split a declaration in two *)
    fun dc_gdecl (d as A.Function(g, rtp, params, SOME(s), specs, is_external, ext)) =
        (* Symbol instance remains the same for definition; no new function environment *)
	(* Add caller id argument to function *)
	[tfm_fundef d]
      | dc_gdecl (d as A.Function(g, rtp, params, NONE, nil, true, ext)) =
	(* external function declaration remains identical, if no contracts *)
	[d]
      | dc_gdecl (d as A.Function(g, rtp, params, NONE, nil, false, ext)) =
	(* no specifications (specs = ni); transform to add argument *)
	[A.Function(g, rtp, params @ [caller_decl], NONE, nil, false, ext)]
      | dc_gdecl (d as A.Function(g, rtp, params, NONE, specs as (_::_), is_external, ext)) =
	(* specifications; create new wrapper for g *)
	let 
	    val g_opt = Funversiontab.lookup g
	    val (g_last, i_last) = case g_opt of NONE => (g,0) | SOME(g_i,i) => (g_i,i)
	    val (g_next, i_next) = next_name (Symbol.name g, i_last+1)
	    val d' = fun_wrapper d g_next
	    val d'' = tfm_fundef d' (* embedded calls go to last version! *)
	    val _ = Symtab.bind(g_next, d'') (* enter in symbol table so Syn.syn works *)
	    val _ = Funversiontab.bind(g, (g_next, i_next)) (* bind latest version *)
            (* add caller id argument to forward declaration *)
	    val d1 = if is_external
		     then d
		     else A.Function(g, rtp, params @ [caller_decl], NONE, specs, is_external, ext)
	in
	    (* preserve first decl, if present, as forward declaration *)
	    case g_opt of NONE => [d1,d''] | SOME _ => [d'']
	end
      (* struct and type definitions *)
      | dc_gdecl d = [d]

   fun dc_gdecls nil = nil
     | dc_gdecls (gdecl::gdecls) =
         dc_gdecl gdecl @ dc_gdecls gdecls

   fun contracts gdecls = dc_gdecls gdecls

end
