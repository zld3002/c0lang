(* C0 Compiler
 * Type checker
 * Frank Pfenning <fp@cs.cmu.edu>
 *) 

signature TYPE_CHECK =
sig

  (* prints error message and raises ErrorMsg.Error if error found *)
  val typecheck : Ast.program * bool -> Ast.program
  val check_all_defined : unit -> unit

  (* typechecker for the top-level interpreter *)
  val typecheck_interpreter : Ast.tp Symbol.table -> Ast.stm -> Ast.stm
      
end

structure TypeChecker :> TYPE_CHECK = 
struct
  structure A = Ast
  structure P = A.Print

  (* for error messages *)
  fun ^^(s1,s2) = s1 ^ "\n[Hint: " ^ s2 ^ "]"
  infix ^^

  (********************************)
  (* Checking properties of types *)
  (********************************)

  (* aid should always be defined if we get here *)
  fun tp_expand (aid) = case Symtab.lookup aid of
      SOME(A.TypeDef(aid, tp, ext)) => tp
      (* NONE should never happen *)

  (* Use symbol table, not type table, because symbol table
   * is constructed while type-checking while type table is
   * constructed while parsing. *)
  fun chk_not_typedef id ext =
      (case Symtab.lookup id
	of SOME(A.TypeDef(t, tp, ext')) =>
	   ( ErrorMsg.error ext ("type name '" ^ Symbol.name id ^ "' used as variable name")
	     ; raise ErrorMsg.Error )
	 | _ => () )

  (* chk_tp tp ext = (), raises Error if tp contains A.Void.
   * Assumes it is not A.Any at the top level. *)
  fun chk_tp (A.Int) ext = ()
    | chk_tp (A.Bool) ext = ()
    | chk_tp (A.String) ext = ()
    | chk_tp (A.Char) ext = ()
    | chk_tp (A.Pointer(A.Any)) ext = () (* can this be asked? *)
    | chk_tp (A.Pointer(tp)) ext = chk_tp tp ext
    | chk_tp (A.Array(tp)) ext = chk_tp tp ext
    | chk_tp (A.StructName(sid)) ext = () (* need not be defined! *)
    | chk_tp (A.TypeName(aid)) ext = chk_tp (tp_expand aid) ext
    | chk_tp (A.Void) ext =
      ( ErrorMsg.error ext ("illegal use of type 'void'"
			    ^^ "'void' can only be used as return type for functions")
      ; raise ErrorMsg.Error )
    (* A.Any must be argument to Pointer *)

  (* chk_known_size tp ext = (), raises Error if we cannot
   * allocate memory of type tp because the size is unknown, that is,
   * is a struct sid that has not (yet) been defined
   * assumes tp is valid (not A.Void or A.Any) *)
  fun chk_known_size (A.Int) ext = ()
    | chk_known_size (A.Bool) ext = ()
    | chk_known_size (A.String) ext = ()
    | chk_known_size (A.Char) ext = ()
    | chk_known_size (A.Pointer _) ext = ()
    | chk_known_size (A.Array _) ext = () (* reference type! *)
    | chk_known_size (A.StructName(sid)) ext =
      (case Structtab.lookup sid
	of NONE => 
	     ( ErrorMsg.error ext ("'struct " ^ Symbol.name sid ^ "' not declared or defined")
	     ; raise ErrorMsg.Error )
	 | SOME (A.Struct(sid', NONE, _, ext')) =>
	     ( ErrorMsg.error ext ("'struct " ^ Symbol.name sid ^ "' declared, but not defined")
	     ; raise ErrorMsg.Error )
         | SOME _ => () (* 'struct sid' is defined *)
      )
    | chk_known_size (A.TypeName(aid)) ext =
        chk_known_size (tp_expand aid) ext
    (* A.Void, A.Any should not be asked *)

  (* chk_small tp ext = (), raises Error if the type is
   * not small, that is, its value cannot be held in a variable *)
  fun chk_small (A.Int) ext = ()
    | chk_small (A.Bool) ext = ()
    | chk_small (A.String) ext = ()
    | chk_small (A.Char) ext = ()
    | chk_small (A.Pointer(A.Any)) ext = () (* needed if "NULL;" is a statement *)
    | chk_small (A.Pointer(tp)) ext = chk_tp tp ext (* component can be any valid type *)
    | chk_small (A.Array(tp)) ext = chk_tp tp ext (* component can be any valid type *)
    | chk_small (tp as A.StructName _) ext =
      ( ErrorMsg.error ext
          ("type " ^ P.pp_tp tp ^ " not small"
	   ^^ "cannot pass or store structs in variables directly; use pointers\n")
      ; raise ErrorMsg.Error )
    | chk_small (A.TypeName(aid)) ext =
        chk_small (tp_expand aid) ext
    | chk_small (A.Void) ext = 
      ( ErrorMsg.error ext ("illegal use of type 'void'"
		            ^^ "type void can only be used as return type for functions")
      ;	raise ErrorMsg.Error )
    (* for *NULL, should not be possible? *)
    | chk_small (A.Any) ext = ()

  (* chk_small_or_void tp ext = (), raises Error if the type
   * is not legal as a function's return type *)
  fun chk_small_or_void (A.Void) ext = ()
    | chk_small_or_void tp ext = chk_small tp ext

  (* tp_equal tp1 tp2 = true if tp1 = tp2
   * assumes the types are valid (allowing void) *)
  fun tp_equal (A.Int) (A.Int) = true
    | tp_equal (A.Bool) (A.Bool) = true
    | tp_equal (A.String) (A.String) = true
    | tp_equal (A.Char) (A.Char) = true
    | tp_equal (A.Pointer(tp1)) (A.Pointer(tp2)) = tp_equal tp1 tp2
    | tp_equal (A.Array(tp1)) (A.Array(tp2)) = tp_equal tp1 tp2
    | tp_equal (tp1 as A.StructName(sid1)) (tp2 as A.StructName(sid2)) =
      (case Symbol.compare(sid1,sid2)
	of EQUAL => true
         | _ => false)
    | tp_equal (A.TypeName(aid1)) (A.TypeName(aid2)) =
      (case Symbol.compare(aid1,aid2)
	of EQUAL => true
	 | _ => tp_equal (tp_expand aid1) (tp_expand aid2))
    | tp_equal (A.TypeName(aid1)) tp2 = tp_equal (tp_expand aid1) tp2
    | tp_equal tp1 (A.TypeName(aid2)) = tp_equal tp1 (tp_expand aid2)
    | tp_equal (A.Void) (A.Void) = true
    | tp_equal tp1 tp2 = false

  (* lub tp1 tp2 = SOME(tp3), the least upper bound of tp1 and tp2.
   *             = NONE if the lub does not exist.
   * The source of subtyping is NULL, which is a pointer of any type.
   * Used when analyzing the type of conditional expressions. *)
  fun lub (A.Pointer(A.Any)) (A.Pointer(A.Any)) = SOME(A.Pointer(A.Any))
    | lub (A.Pointer(tp)) (A.Pointer(A.Any)) = SOME(A.Pointer(tp))
    | lub (A.Pointer(A.Any)) (A.Pointer(tp)) = SOME(A.Pointer(tp))
    (* type definitions never contain A.Pointer(A.Any), so
     * these are handled adequately by tp_equal *)
    (*
    | lub (A.TypeName(aid1)) (A.TypeName(aid2)) =
      (case Symbol.compare(aid1,aid2)
         of EQUAL => A.TypeName(aid1)
          | _ => lub (tp_expand aid1) (tp_expand aid2))
    | lub (A.TypeName(aid1)) tp2 = lub (tp_expand aid1) tp2
    | lub tp1 (A.TypeName(aid2)) = lub tp1 (tp_expand aid2)
    *)
    | lub tp1 tp2 = if tp_equal tp1 tp2
		    then SOME(tp1)
		    else NONE

  (* tp_conv tp1 tp2 = true if tp1 <= tp2, false otherwise
   * The source of subtyping is NULL, which is of type A.Pointer(A.Any).
   * Type definitions cannot contain A.Pointer(A.Any), and
   * A.Pointer(A.Any) can appear only at the top level, so we
   * do not expand tp1. *)
  fun tp_conv (A.Pointer(A.Any)) (A.Pointer(tp)) = true
    | tp_conv (A.Pointer(A.Any)) (A.TypeName(aid)) =
        tp_conv (A.Pointer(A.Any)) (tp_expand aid)
    | tp_conv tp1 tp2 = tp_equal tp1 tp2

  (* tp_comparable tp1 tp2 = true if values of the two types
   * can be compared with '==' and '!=', false otherwise
   * Assumes types are valid, excluding void. *)
  fun tp_comparable (A.Int) (A.Int) = true
    | tp_comparable (A.Bool) (A.Bool) = true
    | tp_comparable (A.String) (A.String) = false
    | tp_comparable (A.Char) (A.Char) = true
    | tp_comparable (A.Pointer(A.Any)) (A.Pointer(tp)) = true
    | tp_comparable (A.Pointer(tp)) (A.Pointer(A.Any)) = true
    | tp_comparable (A.Pointer(tp1)) (A.Pointer(tp2)) = tp_equal tp1 tp2
    | tp_comparable (A.Array(tp1)) (A.Array(tp2)) = tp_equal tp1 tp2
    | tp_comparable (A.TypeName(aid1)) tp2 = tp_comparable (tp_expand aid1) tp2
    | tp_comparable tp1 (A.TypeName(aid2)) = tp_comparable tp1 (tp_expand aid2)
    | tp_comparable tp1 tp2 = false

  (* tp_ordered tp1 tp2 ext = true, if values of the two types
   * can be compared with '<', '<=', '>=', and '>', false otherwise.
   * Assumes types are valid, excluding void. *)
  fun tp_ordered (A.Int) (A.Int) = true
    | tp_ordered (A.Char) (A.Char) = true
    | tp_ordered (A.String) (A.String) = false
    | tp_ordered (A.TypeName(aid1)) tp2 = tp_ordered (tp_expand aid1) tp2
    | tp_ordered tp1 (A.TypeName(aid2)) = tp_ordered tp1 (tp_expand aid2)
    | tp_ordered tp1 tp2 = false

  (* Checking functions which raise Error *)

  (* chk_conv tp1 tp2 ext msg = (), if tp1 <= tp2
   * raises Error otherwise, using msg *)
  fun chk_conv tp1 tp2 ext msg_fun =
      if tp_conv tp1 tp2 then ()
      else ( ErrorMsg.error ext
               (msg_fun () ^ "\n"
		^ "expected: " ^ P.pp_tp tp2 ^ "\n"
		^ "   found: " ^ P.pp_tp tp1)
	   ; raise ErrorMsg.Error )

  (* chk_convs tps tps' ext = (), raises Error if
   * it is not the case that tp <= tp', for each corresponding
   * pair of types in tps and tps'.  Used to compare parameter
   * lists in multiple function declarations and definition. *)
  fun chk_convs nil nil ext msg_fun = ()
    | chk_convs (tp::tps) (tp'::tps') ext msg_fun =
      ( chk_conv tp tp' ext msg_fun
      ;	chk_convs tps tps' ext msg_fun )
    | chk_convs nil (tp'::tps') ext msg_fun =
      ( ErrorMsg.error ext (msg_fun () ^^ "too many arguments")
      ; raise ErrorMsg.Error )
    | chk_convs (tp::tps) nil ext msg_fun =
      ( ErrorMsg.error ext (msg_fun () ^^ "too few arguments")
      ; raise ErrorMsg.Error )

  (***********************************************)
  (* Checking that all variables are initialized *)
  (***********************************************)

  (* We assume for-loops have been eliminated *)

  (* We use Symbol.set to track the sets of identifiers
   * env - environment of declared identifiers
   * defs - set of defined identifiers, where defs subset of env
   *)

  (* is_init defs id ext = (), raises Error if id is not defined in defs *)
  fun is_init defs id ext =
      ( if not (Symbol.member defs id)
	then ( ErrorMsg.error ext ("uninitialized variable '" ^ Symbol.name id ^ "'")
	     ; raise ErrorMsg.Error )
	else () )

  fun env_decls defs nil = defs
    | env_decls defs (A.VarDecl(id, tp, _, _)::decls) =
        env_decls (Symbol.add defs id) decls

  (* lv_exp defs e ext = (), raises Error if some variable in e is not defined in defs *)
  fun lv_exp defs (A.Var(id)) ext = is_init defs id ext
    | lv_exp defs (A.IntConst(c)) ext = ()
    | lv_exp defs (A.StringConst(s)) ext = ()
    | lv_exp defs (A.CharConst(s)) ext = ()
    | lv_exp defs (A.True) ext = ()
    | lv_exp defs (A.False) ext = ()
    | lv_exp defs (A.Null) ext = ()
    | lv_exp defs (A.OpExp(oper, es)) ext = List.app (fn e => lv_exp defs e ext) es
    | lv_exp defs (A.Select(e, f)) ext = lv_exp defs e ext
    | lv_exp defs (A.FunCall(f, es)) ext = List.app (fn e => lv_exp defs e ext) es
    | lv_exp defs (A.Alloc(tp)) ext = ()
    | lv_exp defs (A.AllocArray(tp, e)) ext = lv_exp defs e ext
    | lv_exp defs (A.Result) ext = ()
    | lv_exp defs (A.Length(e)) ext = lv_exp defs e ext
    | lv_exp defs (A.Old(e)) ext = lv_exp defs e ext
    | lv_exp defs (A.Marked(marked_exp)) ext =
        lv_exp defs (Mark.data marked_exp) (Mark.ext marked_exp)

  (* lv_stm env defs s ext = defs'
   * raises Error if a variable used in s is not defined
   * returns defs' (a superset of defs), the set of variables
   * known to be defined after executing s *)
  fun lv_stm env defs (A.Assign(operOpt,A.Marked(marked_exp), e)) ext =
        lv_stm env defs (A.Assign(operOpt, Mark.data(marked_exp), e)) ext
    | lv_stm env defs (A.Assign(NONE, A.Var(id), e)) ext =
        (* 'id = e' *)
        ( lv_exp defs e ext	(* check e *)
	; Symbol.add defs id )	(* define id *)
    | lv_stm env defs (A.Assign(operOpt, lv, e)) ext =
        (* 'lv <op>= e' or ('lv = e' for lv not a variable) *)
        ( lv_exp defs lv ext	(* check lv *)
	; lv_exp defs e ext	(* check e *)
	; defs )		(* nothing new defined *)
    | lv_stm env defs (A.Exp(e)) ext =
        ( lv_exp defs e ext ; defs )
    | lv_stm env defs (A.Seq(ds,ss)) ext =
        (* assuming scoping already taken care of and not shadowing! *)
        let val defs1 = lv_stms (env_decls env ds) (lv_decls env defs ds) ss ext
	in  (* remove symbols declared in ds from defs1 *)
	    Symbol.intersection(defs1, env)
	end
    | lv_stm env defs (A.StmDecl(d)) ext =
        (* assuming this has essentially no scope *)
        (* e.g. sole statement in then- or else-branch of conditional *)
	let val _ = lv_decls env defs [d]
	 (* ignore possible definition made by d *)
         in defs end
    | lv_stm env defs (A.If(e, s1, s2)) ext =
        ( lv_exp defs e ext ;
	  let val defs1 = lv_stm env defs s1 ext
	      val defs2 = lv_stm env defs s2 ext
              (* defs1 and defs2 both include defs *)
	  in
	      (* return only those defined in both branches *)
	      Symbol.intersection (defs1, defs2)
	  end )
    | lv_stm env defs (A.While(e, invs, s)) ext =
        ( lv_exp defs e ext ;	(* check e *)
	  List.app (fn spec => lv_spec defs spec ext) invs ; (* check invs *)
	  ignore (lv_stm env defs s ext) ; (* check body s *)
	  (* ignore anything defined in body, because loop body
           * may not execute at all *)
	  defs )
    (* No A.For ! *)
    | lv_stm env defs (A.Break) ext = env (* return Top = all vars in scope! *)
    | lv_stm env defs (A.Continue) ext = env (* Top *)
    | lv_stm env defs (A.Return(SOME(e))) ext =  (* Top *)
        ( lv_exp defs e ext ; env)
    | lv_stm env defs (A.Return(NONE)) ext = env (* Top *)
    | lv_stm env defs (A.Assert(e1, e2s)) ext =
        ( lv_exp defs e1 ext
	; List.app (fn e => lv_exp defs e ext) e2s 
	; defs )
    | lv_stm env defs (A.Error e) ext = 
        ( lv_exp defs e ext
        ; defs)
    | lv_stm env defs (A.Anno(specs)) ext =
        ( List.app (fn spec => lv_spec defs spec ext) specs
	; defs )
    | lv_stm env defs (A.Markeds(marked_stm)) ext =
        lv_stm env defs (Mark.data marked_stm) (Mark.ext marked_stm)

  (* lv_stms env defs ss ext = defs', as in lv_stm for statement sequence *)
  and lv_stms env defs nil ext = defs
    | lv_stms env defs (s::ss) ext =
      let val defs1 = lv_stm env defs s ext
      in
	  lv_stms env defs1 ss ext
      end

  (* lv_decls env defs ds = defs'
   * adds the set of symbols defined by the declarations ds to defs
   * and returns defs' (superset defs).  Raises Error if one of the
   * initializers in ds uses an uninitialized variables *)
  and lv_decls env defs nil = defs
    | lv_decls env defs (A.VarDecl(id, tp, NONE, _)::decls) =
        (* variable is *not* defined here, only declared *)
        lv_decls (Symbol.add env id) defs decls
    | lv_decls env defs (A.VarDecl(id, tp, SOME(e), ext)::decls) =
        ( lv_exp defs e ext ;
	  lv_decls (Symbol.add env id) (Symbol.add defs id) decls )

  (* lv_specs defs spec ext - like lv_exp *)
  and lv_spec defs (A.Requires(e, ext')) ext = lv_exp defs e ext'
    | lv_spec defs (A.Ensures(e, ext')) ext = lv_exp defs e ext'
    | lv_spec defs (A.LoopInvariant(e, ext')) ext = lv_exp defs e ext'
    | lv_spec defs (A.Assertion(e, ext')) ext = lv_exp defs e ext'

  (* lv_params defs decls = defs', adding all symbols declared
   * in decls to defs, since function parameters are initialized
   * by the function call arguments *)
  fun lv_params defs nil = defs
    | lv_params defs (A.VarDecl(id, tp, NONE, _)::decls) =
        lv_params (Symbol.add defs id) decls

  fun lv_fun (A.Function(g, tp, params, SOME(s), _, _, ext)) =
      (* function definition *)
      let (* fun params are initialized, but not locals *)
	  val defs0 = lv_params Symbol.null params
	  val env0 = defs0 
	  val _ = lv_stm env0 defs0 s ext
          (* could warn here: variables declared, but never initialized *)
      in
	  ()
      end
    | lv_fun (fdecl as A.Function _) =
      (* function declaration - nothing to check *)
      ()

  (* Check for the absense of returns in a statment *)
  (* Used in coin, the interactive interpreter *)
  fun nr_stm (A.Assign _) ext = ()
    | nr_stm (A.Exp _) ext = ()
    | nr_stm (A.Seq(_, ss)) ext = ( List.app (fn s => nr_stm s ext) ss )
    | nr_stm (A.StmDecl _) ext = ()
    | nr_stm (A.If(_,s1,s2)) ext = ( nr_stm s1 ext ; nr_stm s2 ext )
    | nr_stm (A.While(_, _, s)) ext = ( nr_stm s ext)
    | nr_stm (A.For(s1, _, s2, _, s3)) ext =
        ( nr_stm s1 ext ; nr_stm s2 ext ; nr_stm s3 ext )
    | nr_stm (A.Continue) ext = ()
    | nr_stm (A.Break) ext = ()
    | nr_stm (A.Return _) ext =
        ( ErrorMsg.error ext ("return not allowed") ; raise ErrorMsg.Error )
    | nr_stm (A.Assert _) ext = ()
    | nr_stm (A.Error _) ext = ()
    | nr_stm (A.Anno _) ext = ()
    | nr_stm (A.Markeds(marked_stm)) ext =
        ( nr_stm (Mark.data marked_stm) (Mark.ext marked_stm) )

  (****************************************)
  (* Checking annotations are well-formed *)
  (****************************************)

  (* Check we do not assign to variables appearing in postcondition
   * pvars - postcondition variables *)

  (* pv_exp pvars e = pvars', where pvars' = pvars + vars(e)
   * Variables in arguments to \old(_) are evaluated in initial
   * environment, so they are ignored here *)
  fun pv_exp pvars (A.Var(x)) = Symbol.add pvars x
    | pv_exp pvars (A.IntConst _) = pvars
    | pv_exp pvars (A.StringConst _) = pvars
    | pv_exp pvars (A.CharConst _) = pvars
    | pv_exp pvars (A.True) = pvars
    | pv_exp pvars (A.False) = pvars
    | pv_exp pvars (A.Null) = pvars
    | pv_exp pvars (A.OpExp(oper, es)) = pv_exps pvars es
    | pv_exp pvars (A.Select(e, f)) = pv_exp pvars e
    | pv_exp pvars (A.FunCall(g, es)) = pv_exps pvars es
    | pv_exp pvars (A.Alloc _) = pvars
    | pv_exp pvars (A.AllocArray(tp, e)) = pv_exp pvars e
    | pv_exp pvars (A.Result) = pvars
    | pv_exp pvars (A.Length(e)) = pv_exp pvars e
    (* variables in \old(e) are guarded and create no conflict *)
    | pv_exp pvars (A.Old(e)) = pvars
    | pv_exp pvars (A.Marked(marked_exp)) =
        pv_exp pvars (Mark.data marked_exp)
  and pv_exps pvars nil = pvars
    | pv_exps pvars (e::es) = pv_exps (pv_exp pvars e) es

  fun pv_spec pvars (A.Requires _) = pvars
    | pv_spec pvars (A.Ensures(e, _)) = pv_exp pvars e
    | pv_spec pvars (A.LoopInvariant _) = pvars
    | pv_spec pvars (A.Assertion _) = pvars

  fun pv_specs pvars nil = pvars
    | pv_specs pvars (spec::specs) =
        pv_specs (pv_spec pvars spec) specs

  (* chk_unassigned_lv pvars lv ext = (), raises Error if
   * lv is a variable occurring in pvars *)
  fun chk_unassigned_lv pvars (A.Var(x)) ext =
      if Symbol.member pvars x
      then ( ErrorMsg.error ext ("cannot assign to variable '" ^ Symbol.name x ^ "' used in @ensures annotation")
           ; raise ErrorMsg.Error )
      else ()
   | chk_unassigned_lv pvars (A.Marked(marked_exp)) ext =
       chk_unassigned_lv pvars (Mark.data marked_exp) (Mark.ext marked_exp)
   | chk_unassigned_lv pvars lv ext = ()

  (* chk_unassigned pvars s ext = (), raises Error if s
   * assigns to a variable occurring in pvars *)
  fun chk_unassigned pvars (A.Assign(_, lv, e)) ext =
        chk_unassigned_lv pvars lv ext
    | chk_unassigned pvars (A.Exp _) ext = ()
    | chk_unassigned pvars (A.Seq(ds, ss)) ext =
        List.app (fn s => chk_unassigned pvars s ext) ss
    | chk_unassigned pvars (A.StmDecl _) ext = ()
    | chk_unassigned pvars (A.If(e, s1, s2)) ext =
        ( chk_unassigned pvars s1 ext
	; chk_unassigned pvars s2 ext )
    | chk_unassigned pvars (A.While(e, _, s)) ext =
        chk_unassigned pvars s ext
    | chk_unassigned pvars (A.For(s1, e, s2, _, s3)) ext =
        ( chk_unassigned pvars s1 ext
	; chk_unassigned pvars s2 ext
	; chk_unassigned pvars s3 ext )
    | chk_unassigned pvars (A.Continue) ext = ()
    | chk_unassigned pvars (A.Break) ext = ()
    | chk_unassigned pvars (A.Return _) ext = ()
    | chk_unassigned pvars (A.Assert _) ext = ()
    | chk_unassigned pvars (A.Error _) ext = ()
    | chk_unassigned pvars (A.Anno _) ext = ()
    | chk_unassigned pvars (A.Markeds(marked_stm)) ext =
        chk_unassigned pvars (Mark.data marked_stm) (Mark.ext marked_stm)

  (* Checking that annotations are used correctly: @requires and @ensures
   * in function headers, @loop_invariant in loop headers, and @assert
   * before statements.  Also, \old(_) and \result can only be used in
   * @ensures annotations *)

  structure R =
  struct
    datatype rtspec =
        ORDINARY		(* in ordinary expression *)
      | FUNCONTRACT		(* in function contract *)
      | LOOPINV			(* in @loop_invariant *)
      | ASSERTION		(* in @assert *)
      | PRECOND			(* in @requires *)
      | POSTCOND		(* in @ensures *)

    fun rt_error ext msg =
	( ErrorMsg.error ext msg ; raise ErrorMsg.Error )
  end

  (* rt_exp e cond ext = (), raises Error if the rtspec cond is violated
   * by the expression *)
  fun rt_exp (A.Var _) cond ext = ()
    | rt_exp (A.IntConst _) cond ext = ()
    | rt_exp (A.StringConst _) cond ext = ()
    | rt_exp (A.CharConst _) cond ext = ()
    | rt_exp (A.True) cond ext = ()
    | rt_exp (A.False) cond ext = ()
    | rt_exp (A.Null) cond ext = ()
    | rt_exp (A.OpExp(oper, es)) cond ext =
        List.app (fn e => rt_exp e cond ext) es
    | rt_exp (A.Select(e, f)) cond ext =
        rt_exp e cond ext
    | rt_exp (A.FunCall(g, es)) cond ext =
        List.app (fn e => rt_exp e cond ext) es
    | rt_exp (A.Alloc _) cond ext = ()
    | rt_exp (A.AllocArray(tp, e)) cond ext = rt_exp e cond ext
    | rt_exp (A.Result) (R.ORDINARY) ext =
        R.rt_error ext ("\\result illegal in ordinary expression" ^^ "use only in @ensures annnotations")
    | rt_exp (A.Result) (R.ASSERTION) ext =
        R.rt_error ext ("\\result illegal in @assert" ^^ "use only in @ensures annotations")
    | rt_exp (A.Result) (R.LOOPINV) ext =
        R.rt_error ext ("\\result illegal in @loop_invariant" ^^ "use only in @ensures annotations")
    | rt_exp (A.Result) (R.PRECOND) ext =
        R.rt_error ext ("\\result illegal in @requires" ^^ "use only in @ensures annotations")
    | rt_exp (A.Result) (R.POSTCOND) ext = ()
    | rt_exp (A.Length(e)) (R.ORDINARY) ext =
        R.rt_error ext ("\\length(e) illegal in ordinary expression" ^^ "use only in annotations")
    | rt_exp (A.Length(e)) _ ext = ()
    | rt_exp (A.Old(e)) (R.ORDINARY) ext =
        R.rt_error ext ("\\old(e) illegal in ordinary expression" ^^ "use only in @ensures annotations")
    | rt_exp (A.Old(e)) (R.ASSERTION) ext =
        R.rt_error ext ("\\old(e) illegal in @assert annotation" ^^ "use only in @ensures annotations")
    | rt_exp (A.Old(e)) (R.LOOPINV) ext =
        R.rt_error ext ("\\old(e) illegal in @loop_invariant" ^^ "use only in @ensures annotations")
    | rt_exp (A.Old(e)) (R.PRECOND) ext =
        R.rt_error ext ("\\old(e) illegal in @requires" ^^ "use only in @ensures annotations")
    | rt_exp (A.Old(e)) (R.POSTCOND) ext = ()
    | rt_exp (A.Marked(marked_exp)) cond ext =
        rt_exp (Mark.data marked_exp) cond (Mark.ext marked_exp)

  (* rt_spec spec cond ext = (), raises Error if the rtspec cond is violated
   * by the specification spec *)
  fun rt_spec (A.Requires(e, ext')) (R.ASSERTION) ext =
        R.rt_error ext' ("@requires illegal in statement annotation" ^^ "use only in function contracts")
    | rt_spec (A.Requires(e, ext')) (R.FUNCONTRACT) ext =
        rt_exp e R.PRECOND ext'
    | rt_spec (A.Requires(e, ext')) (R.LOOPINV) ext =
        R.rt_error ext' ("@requires illegal in loop invariant" ^^ "use only in function contracts")
    | rt_spec (A.Ensures(e, ext')) (R.ASSERTION) ext =
        R.rt_error ext' ("@ensures illegal in statement annotation" ^^ "use only in function contracts")
    | rt_spec (A.Ensures(e, ext')) (R.FUNCONTRACT) ext =
        rt_exp e R.POSTCOND ext'
    | rt_spec (A.Ensures(e, ext')) (R.LOOPINV) ext =
        R.rt_error ext' ("@ensures illegal in loop invariant" ^^ "use only in function contracts")
    | rt_spec (A.LoopInvariant(e, ext')) (R.ASSERTION) ext =
        R.rt_error ext' ("@loop_invariant illegal statement annotation" ^^ "use only for loops")
    | rt_spec (A.LoopInvariant(e, ext')) (R.FUNCONTRACT) ext =
        R.rt_error ext' ("@loop_invariant illegal in function contracts;" ^^ "use only for loops")
    | rt_spec (A.LoopInvariant(e, ext')) (R.LOOPINV) ext =
        rt_exp e R.LOOPINV ext'
    | rt_spec (A.Assertion(e, ext')) (R.ASSERTION) ext =
	rt_exp e R.ASSERTION ext'
    | rt_spec (A.Assertion(e, ext')) (R.FUNCONTRACT) ext =
        R.rt_error ext' ("@assert illegal in function contracts" ^^ "use only in statment annotations")
    | rt_spec (A.Assertion(e, ext')) (R.LOOPINV) ext =
        R.rt_error ext' ("@assert illegal in loop invariants" ^^ "use only in statement annotations")

  (* rt_stm s ext = (), raises Error if annotations or special expressions
   * (\length, \old, \result) are used incorrectly in s *)
  fun rt_stm (A.Assign(operOpt, lv, e)) ext =
        ( rt_exp lv R.ORDINARY ext
	; rt_exp e R.ORDINARY ext )
    | rt_stm (A.Exp(e)) ext =
        rt_exp e R.ORDINARY ext
    | rt_stm (A.Seq(ds, ss)) ext =
        ( List.app (fn d => rt_decl d ext) ds
	; List.app (fn s => rt_stm s ext) ss )
    | rt_stm (A.StmDecl(d)) ext =
        rt_decl d ext
    | rt_stm (A.If(e,s1,s2)) ext =
        ( rt_exp e R.ORDINARY ext ; rt_stm s1 ext ; rt_stm s2 ext )
    | rt_stm (A.While(e, invs, s)) ext =
        ( rt_exp e R.ORDINARY ext
	; List.app (fn spec => rt_spec spec R.LOOPINV ext) invs
	; rt_stm s ext )
    | rt_stm (A.For(s1, e, s2, invs, s3)) ext =
        ( rt_stm s1 ext ; rt_exp e R.ORDINARY ext
	; rt_stm s2 ext ; List.app (fn spec => rt_spec spec R.LOOPINV ext) invs
	; rt_stm s3 ext )
    | rt_stm (A.Continue) ext = ()
    | rt_stm (A.Break) ext = ()
    | rt_stm (A.Return(NONE)) ext = ()
    | rt_stm (A.Return(SOME(e))) ext =
        rt_exp e R.ORDINARY ext
    | rt_stm (A.Assert(e1, e2s)) ext =
        ( rt_exp e1 R.ORDINARY ext
	; List.app (fn e => rt_exp e R.ORDINARY ext) e2s )
    | rt_stm (A.Error e) ext = rt_exp e R.ORDINARY ext
    | rt_stm (A.Anno(specs)) ext =
        List.app (fn spec => rt_spec spec R.ASSERTION ext) specs
    | rt_stm (A.Markeds(marked_stm)) ext =
        rt_stm (Mark.data marked_stm) (Mark.ext marked_stm)

  and rt_decl (A.VarDecl(id, tp, NONE, ext')) ext = ()
    | rt_decl (A.VarDecl(id, tp, SOME(e), ext')) ext =
        rt_exp e R.ORDINARY ext'

  fun rt_fdecl (A.Function(g, rtp, params, SOME(s), specs, _, ext)) =
      let 
	  val () = rt_stm s ext (* proper use of \length, \result, \old, and annotations *)
          (* pvars = list of variables appearing unguarded in postconditions *)
	  val pvars = pv_specs Symbol.null specs
	  val () = chk_unassigned pvars s ext (* check no assignment to vars in postconditions *)
	  val () = List.app (fn spec => rt_spec spec R.FUNCONTRACT ext) specs
		  (* proper use of \result, \old, and annotations in function contracts *)
      in
	  ()
      end
    | rt_fdecl (A.Function(f, rtp, params, NONE, specs, _, ext)) =
      (* check function contracts *)
      let
	  val () = List.app (fn spec => rt_spec spec R.FUNCONTRACT ext) specs
      in
	  ()
      end
 
  (*****************)
  (* Type checking *)
  (*****************)

  fun var_type env id ext =
      (case Symbol.look env id
	of NONE => ( ErrorMsg.error ext ("undeclared variable '" ^ Symbol.name id ^ "'") ;
		     raise ErrorMsg.Error )
	 | SOME(tp) => tp)

  fun syn_field nil f ext =
        ( ErrorMsg.error ext ("undeclared field '" ^ Symbol.name f ^ "'")
	; raise ErrorMsg.Error )
    | syn_field (A.Field(f',tp,_)::fields) f ext =
      (case Symbol.compare (f',f)
         of EQUAL => tp
          | _ => syn_field fields f ext)

  fun expand_def (A.TypeName(aid)) = expand_def (tp_expand aid)
    | expand_def (tp) = tp

  (* functions syn_<cat> synthesize the type of an exp or exps.
   * functions chk_<cat> check that a <cat> is well-typed.
   * Both raise Error if not well-typed
   * As a side-effect, we Symset.add any function name that is used
   * and declared, but not yet defined.
   * The functions use Symtab to look up function and type names
   *)

  (* syn_exp : Ast.tp Symbol.table -> Ast.exp -> Mark.ext option -> tp *)
  (* syn_exp env e ext = tp, if env |- e : tp.  Raises Error if not well-typed *)
  fun syn_exp env (A.Var(id)) ext = var_type env id ext
    | syn_exp env (A.IntConst(c)) ext = A.Int
    | syn_exp env (A.StringConst(s)) ext = A.String
    | syn_exp env (A.CharConst(c)) ext = A.Char
    | syn_exp env (A.True) ext = A.Bool
    | syn_exp env (A.False) ext = A.Bool
    | syn_exp env (A.Null) ext = A.Pointer(A.Any)
    | syn_exp env (A.OpExp(A.SUB, [e1,e2])) ext =
      (case (syn_exp_expd env e1 ext)
	 of A.Array(tp) => ( chk_exp env e2 A.Int ext ; tp )
          | tp => ( ErrorMsg.error ext ("subject of indexing '[...]' not an array\n"
					^ "inferred type " ^ P.pp_tp tp)
		 ; raise ErrorMsg.Error ))
    | syn_exp env (A.OpExp(A.DEREF, [e1])) ext =
      (case (syn_exp_expd env e1 ext)
         of A.Pointer(A.Any) => ( ErrorMsg.error ext ("cannot dereference NULL")
				; raise ErrorMsg.Error )
	  | A.Pointer(tp) => tp
          | tp => ( ErrorMsg.error ext ("subject of '*' or '->' not a pointer\n"
					^ "inferred type " ^ P.pp_tp tp)
		 ; raise ErrorMsg.Error ))
    | syn_exp env (A.OpExp(A.EQ, [e1,e2])) ext =
        ( chk_comparison env e1 e2 ext ; A.Bool )
    | syn_exp env (A.OpExp(A.NOTEQ, [e1,e2])) ext =
        ( chk_comparison env e1 e2 ext ; A.Bool )
    | syn_exp env (A.OpExp(A.LOGNOT, [e])) ext =
        ( chk_exp env e A.Bool ext ; A.Bool )
    | syn_exp env (A.OpExp(A.LESS, [e1, e2])) ext =
        ( chk_ordered env e1 e2 ext ; A.Bool)
    | syn_exp env (A.OpExp(A.LEQ, [e1, e2])) ext =
        ( chk_ordered env e1 e2 ext ; A.Bool)
    | syn_exp env (A.OpExp(A.GREATER, [e1, e2])) ext =
        ( chk_ordered env e1 e2 ext ; A.Bool)
    | syn_exp env (A.OpExp(A.GEQ, [e1, e2])) ext =
        ( chk_ordered env e1 e2 ext ; A.Bool)
    | syn_exp env (A.OpExp(A.LOGAND, [e1, e2])) ext =
        ( chk_exp env e1 A.Bool ext
	; chk_exp env e2 A.Bool ext
	; A.Bool )
    | syn_exp env (A.OpExp(A.LOGOR, [e1, e2])) ext =
        ( chk_exp env e1 A.Bool ext
	; chk_exp env e2 A.Bool ext 
	; A.Bool )
    | syn_exp env (A.OpExp(A.COND, [e1, e2, e3])) ext =
      let val () = chk_exp env e1 A.Bool ext
	  val tp2 = syn_exp env e2 ext
	  val tp3 = syn_exp env e3 ext
      in
	  case lub tp2 tp3
	   of NONE => ( ErrorMsg.error ext ("branches of conditional expression have different types\n"
					    ^ "then branch: " ^ P.pp_tp tp2 ^ "\n"
					    ^ "else branch: " ^ P.pp_tp tp3)
		      ; raise ErrorMsg.Error )
	    | SOME(tp) => tp
      end 
    | syn_exp env (A.OpExp(oper,es)) ext =
      (* all remaining operators are on integers only *)
      ( List.app (fn e => chk_exp env e A.Int ext) es
      ; A.Int )
    | syn_exp env (A.Select(e,f)) ext =
      (case (syn_exp_expd env e ext)
	of A.StructName(sid) =>
	   (case Structtab.lookup sid
             of SOME(A.Struct(sid', SOME(fields), _, ext')) => syn_field fields f ext
              | SOME(A.Struct(sid', NONE, _, ext')) =>
		  ( ErrorMsg.error ext ("'struct " ^ Symbol.name sid ^ "' declared but not defined")
		  ; raise ErrorMsg.Error )
              | NONE => ( ErrorMsg.error ext ("'struct " ^ Symbol.name sid ^ "' not defined")
			; raise ErrorMsg.Error )
           )
	 | tp => ( ErrorMsg.error ext ("subject of '->' not a struct pointer, or of '.' not a struct"
				       ^ "inferred type " ^ P.pp_tp tp)
		 ; raise ErrorMsg.Error ))
    | syn_exp env (A.FunCall(g, es)) ext =
      ( case Symbol.look env g
	 of SOME _ => ( ErrorMsg.error ext ("function name '" ^ Symbol.name g ^ "' shadowed by local variable")
		      ; raise ErrorMsg.Error )
	  | _ => ()
      ; case Symtab.lookup g
	 of NONE => ( ErrorMsg.error ext ("undeclared function '" ^ Symbol.name g ^ "'") ;
		      raise ErrorMsg.Error )
	  | SOME(A.Function(g', rtp, params, bodyOpt, _, _, _)) =>
	    ( chk_exps env es params ext
	    (* if bodyOpt = NONE, then g has been used, but is not yet defined *)
	    ; case bodyOpt of NONE => Symset.add g | SOME _ => ()
	    ; rtp )
          | SOME(A.TypeDef(aid, tp, ext')) =>
	    ( ErrorMsg.error ext ("cannot use type name '" ^ Symbol.name aid ^ "' as function name")
	    ; raise ErrorMsg.Error ) )
    | syn_exp env (A.Alloc(tp)) ext =
      ( chk_tp tp ext ; chk_known_size tp ext
      ; A.Pointer(tp) )
    | syn_exp env (A.AllocArray(tp,e)) ext = 
      ( chk_tp tp ext ; chk_known_size tp ext ; chk_exp env e A.Int ext
      ; A.Array(tp) )
    | syn_exp env (A.Result) ext =
        var_type env (Symbol.symbol "\\result") ext
    | syn_exp env (A.Length(e)) ext =
      (case (syn_exp_expd env e ext)
	of A.Array(tp) => A.Int
	 | _ => ( ErrorMsg.error ext ("argument to \\length not an array")
		 ; raise ErrorMsg.Error ))
    | syn_exp env (A.Old(e)) ext =
      (* check something about e here? *)
        syn_exp env e ext
    | syn_exp env (A.Marked(marked_exp)) ext =
        syn_exp env (Mark.data marked_exp) (Mark.ext marked_exp)

  (* syn_exp_expd env e ext = tp with env |- e : tp,
   * where tp is expanded as necessary so it is not a typename aid *)
  and syn_exp_expd env e ext = expand_def (syn_exp env e ext)

  and syn_exps env nil ext = nil
    | syn_exps env (e::es) ext =
        syn_exp env e ext::syn_exps env es ext

  (* chk_exp env e tp ext = () if env |- e : tp, raises Error otherwise *)
  and chk_exp env e tp ext =
      let val tp1 = syn_exp env e ext
      in
	  if tp_conv tp1 tp then ()
	  else ( ErrorMsg.error ext ("type mismatch\n"
				     ^ "expected: " ^ P.pp_tp tp ^ "\n"
				     ^ "   found: " ^ P.pp_tp tp1)
	       ; raise ErrorMsg.Error )
      end 

  (* chk_exps env es ds ext = () if env |- es : ds, raises Error otherwise
   * ds must be function parameter declarations *)
  and chk_exps env nil nil ext = ()
    | chk_exps env (e::es) (A.VarDecl(x,tp,NONE,ext')::tps) ext =
      ( chk_exp env e tp ext
      ; chk_exps env es tps ext )
    | chk_exps env (e::es) nil ext =
      ( ErrorMsg.error ext "too many arguments in function call"
      ; raise ErrorMsg.Error )
    | chk_exps env nil (tp::tps) ext =
      ( ErrorMsg.error ext "too few arguments in function call"
      ; raise ErrorMsg.Error )

  (* chk_comparison env e1 e2 ext = (), raises error
   * if e1 or e2 are not well-typed, or their types don't
   * admit comparison with '==' or '!=" *)
  and chk_comparison env e1 e2 ext =
      let val tp1 = syn_exp env e1 ext
	  val tp2 = syn_exp env e2 ext
      in
	  if tp_comparable tp1 tp2 then ()
	  else if tp_equal tp1 A.String andalso tp_equal tp2 A.String
	  then ( ErrorMsg.error ext ("cannot compare strings with '==' or '!='"
				     ^^ "use string_equal in library <string>" )
		 ; raise ErrorMsg.Error )
	  else ( ErrorMsg.error ext ("comparison with '==' or '!=' with incompatible types\n"
				     ^ " left-hand side: " ^ P.pp_tp tp1 ^ "\n"
				     ^ "right-hand side: " ^ P.pp_tp tp2)
		 ; raise ErrorMsg.Error )
      end

  (* chk_ordered env e1 e2 ext = (), raises error
   * if e1 or e2 are not well-typed, or their types don't
   * admit comparison with '<', '<=', '>=', or '>'" *)
  and chk_ordered env e1 e2 ext =
      let val tp1 = syn_exp env e1 ext
	  val tp2 = syn_exp env e2 ext
      in
	  if tp_ordered tp1 tp2 then ()
	  else if tp_equal tp1 A.String andalso tp_equal tp2 A.String
	  then ( ErrorMsg.error ext ("cannot compare strings with '<' '<=' '>=' '>'"
				     ^^ "use string_compare in library <string>" )
		 ; raise ErrorMsg.Error )
	  else ( ErrorMsg.error ext ("comparison with '<' '<=' '>=' '>' with incomparable types\n"
				     ^ " left-hand side: " ^ P.pp_tp tp1 ^ "\n"
				     ^ "right-hand side: " ^ P.pp_tp tp2)
		 ; raise ErrorMsg.Error )
      end

  (* chk_lval e ext = () if e is a legal lvalue, raises Error otherwise *)
  fun chk_lval (A.Var _) ext = ()
    | chk_lval (A.OpExp(A.DEREF, [e])) ext = chk_lval e ext
    | chk_lval (A.OpExp(A.SUB, [e1,e2])) ext = chk_lval e1 ext
    | chk_lval (A.Select(e, f)) ext = chk_lval e ext
    | chk_lval (A.Marked(marked_exp)) ext =
        chk_lval (Mark.data marked_exp) (Mark.ext marked_exp)
    | chk_lval e ext = ( ErrorMsg.error ext
		           ("left-hand side of assignment not a legal lvalue"
			    ^^ "an lvalue l must be a variable or of the form *l, l[e], l.f, or l->f")
		       ; raise ErrorMsg.Error )

  (* chk_stm env s rtp loop ext = () if s is a well-typed statment
   * in a function body with return type rtp
   * and inside a loop if loop = true (to check valid break and continue) *)
  fun chk_stm env (A.Assign(NONE,lv,e)) rtp loop ext =
      let val () = chk_lval lv ext
          val tp1 = syn_exp env lv ext
          val () = chk_small tp1 ext (* must be small value *)
	  val tp2 = syn_exp env e ext
      in
	  if tp_conv tp2 tp1 then ()
	  else ( ErrorMsg.error ext ("sides of assignment have different type\n"
				     ^ " left-hand side: " ^ P.pp_tp tp1 ^ "\n"
				     ^ "right-hand side: " ^ P.pp_tp tp2)
	       ; raise ErrorMsg.Error )
      end
    | chk_stm env (A.Assign(SOME(oper),lv,e)) rtp loop ext =
      (* compound assignment operators all on type int *)
      let val () = chk_lval lv ext
          val () = chk_exp env lv A.Int ext
	  val () = chk_exp env e A.Int ext
      in
	  ()
      end
    | chk_stm env (A.Exp(e)) rtp loop ext =
      let val tp = syn_exp env e ext
	  val () = chk_small_or_void tp ext (* must be of small type or void *)
      in
	  ()
      end
    | chk_stm env (A.Return(SOME(e))) rtp loop ext =
      let val tp = syn_exp env e ext
      in if tp_conv A.Void rtp
	 then ( ErrorMsg.error ext ("function returning void must invoke 'return', not 'return e'")
	      ; raise ErrorMsg.Error )
	 else if tp_conv tp rtp then ()
	 else ( ErrorMsg.error ext ("type mismatch\n"
				    ^ "expected return type: " ^ P.pp_tp rtp ^ "\n"
				    ^ "   found return type: " ^ P.pp_tp tp)
	      ; raise ErrorMsg.Error )
      end 
    | chk_stm env (A.Return(NONE)) rtp loop ext =
      if tp_conv A.Void rtp then ()
      else ( ErrorMsg.error ext ("type mismatch\n"
				 ^ "expected return type: " ^ P.pp_tp rtp ^ "\n"
				 ^ "   found return type: void")
	   ; raise ErrorMsg.Error )
    | chk_stm env (A.Assert(e1, e2s)) rtp loop ext =
        ( chk_exp env e1 A.Bool ext ;
	  List.app (fn e => chk_exp env e A.String ext) e2s )
    | chk_stm env (A.Error e) rtp loop ext = 
        chk_exp env e A.String ext
    | chk_stm env (A.Anno(specs)) rtp loop ext =
        List.app (fn spec => chk_spec env spec ext) specs
    | chk_stm env (A.Seq(ds,ss)) rtp loop ext =
        let val env' = syn_decls env ds
	in
            chk_stms env' ss rtp loop ext
	end
    | chk_stm env (A.StmDecl(d)) rtp loop ext =
        ignore (syn_decls env [d]) (* Interpreter's toplevel only? *)
    | chk_stm env (A.If(e,s1,s2)) rtp loop ext =
      ( chk_exp env e A.Bool ext ;
	chk_stm env s1 rtp loop ext ;
	chk_stm env s2 rtp loop ext )
    | chk_stm env (A.While(e, invs, s)) rtp loop ext =
      ( chk_exp env e A.Bool ext
      ; List.app (fn spec => chk_spec env spec ext) invs
      ; chk_stm env s rtp true ext )	(* this call always inside loop *)
    | chk_stm env (A.For(_, _, A.StmDecl(d), _, _)) rtp loop ext =
      ( ErrorMsg.error ext ("declaration not meaningful as step of for-loop") ;
	raise ErrorMsg.Error )      
    | chk_stm env (A.For(A.StmDecl(d), e, s2, invs, s3)) rtp loop ext =
      let val env' = syn_decls env [d]
	  val () = chk_exp env' e A.Bool ext
	  val () = chk_stm env' s2 rtp loop ext (* must be simple statement, not continue or break *)
	  val () = List.app (fn spec => chk_spec env' spec ext) invs
	  val () = chk_stm env' s3 rtp true ext (* this call always inside loop *)
      in
	  ()
      end
    | chk_stm env (A.For(s1, e, s2, invs, s3)) rtp loop ext =
      (* s1 not a declaration *)
      ( chk_stm env s1 rtp loop ext
      ; chk_exp env e A.Bool ext
      ;	chk_stm env s2 rtp loop ext (* must be simple statement; not continue or break *)
      ; List.app (fn spec => chk_spec env spec ext) invs
      ; chk_stm env s3 rtp true ext ) (* this call always inside loop *)
    | chk_stm env (A.Continue) rtp loop ext =
      if loop then ()
      else ( ErrorMsg.error ext ("continue statement not inside a for- or while-loop")
	   ; raise ErrorMsg.Error )
    | chk_stm env (A.Break) rtp loop ext =
      if loop then ()
      else ( ErrorMsg.error ext ("break statement not inside a for- or while-loop")
	   ; raise ErrorMsg.Error )
    | chk_stm env (A.Markeds(marked_stm)) rtp loop ext =
        chk_stm env (Mark.data marked_stm) rtp loop (Mark.ext marked_stm)

  (* chk_stms env ss rtp loop ext = (), raises Error as in chk_stm *)
  and chk_stms env nil rtp loop ext = ()
    | chk_stms env (s::ss) rtp loop ext = 
      ( chk_stm env s rtp loop ext ; chk_stms env ss rtp loop ext )

  (* syn_decls env decls = env', raises Error if not well-typed.
   * env' adds declarations from decls to env *)
  and syn_decls env nil = env
    | syn_decls env (A.VarDecl(id, tp, NONE, ext)::decls) =
      ( chk_not_typedef id ext	(* check that id is not a type name *)
      ; chk_small tp ext	(* check that type is well-formed and small *)
      ; case Symbol.look env id
	 of NONE => syn_decls (Symbol.bind env (id, tp)) decls
          | SOME _ => ( ErrorMsg.error ext ("variable '" ^ Symbol.name id ^ "' declared twice")
		      ; raise ErrorMsg.Error ) )
    | syn_decls env (A.VarDecl(id, tp, SOME(e), ext)::decls) =
      ( chk_not_typedef id ext	(* check that id is not a defined type symbol *)
      ; chk_small tp ext
      ; chk_exp env e tp ext
      ; case Symbol.look env id
	 of NONE => syn_decls (Symbol.bind env (id, tp)) decls
	  | SOME _ => ( ErrorMsg.error ext ("variable '" ^ Symbol.name id ^ "' declared twice")
		      ; raise ErrorMsg.Error ) )

  and chk_spec env (A.Requires(e, ext')) ext =
        chk_exp env e A.Bool ext'
    | chk_spec env (A.Ensures(e, ext')) ext =
        chk_exp env e A.Bool ext'
    | chk_spec env (A.LoopInvariant(e, ext')) ext =
        chk_exp env e A.Bool ext'
    | chk_spec env (A.Assertion(e, ext')) ext =
        chk_exp env e A.Bool ext'

  fun chk_fun (A.Function(g, rtp, params, SOME(s), specs, _, ext)) =
      let 
	  val () = chk_small_or_void rtp ext
	  val env0 = syn_decls Symbol.empty params
	  val () = chk_stm env0 s rtp false ext
	  val result = Symbol.symbol "\\result" (* for type of A.Result; only in @ensures *)
	  val env1 = Symbol.bind env0 (result, rtp)
	  val () = List.app (fn spec => chk_spec env1 spec ext) specs
      in
	  ()
      end
    | chk_fun (A.Function(f, rtp, params, NONE, specs, _, ext)) =
      let
	  val () = chk_small_or_void rtp ext
	  val env0 = syn_decls Symbol.empty params
	  val result = Symbol.symbol "\\result" (* for type of A.Result; only in @ensures *)
	  val env1 = Symbol.bind env0 (result, rtp)
	  val () = List.app (fn spec => chk_spec env1 spec ext) specs
      in
	  ()
      end

  (* elim_for s step_opts ext = s', where for loops have been replace by while loops 
   * step_opts is a stack of optional simple step statements, with the to
   * pertaining to the current loop (while or for).
   * A 'continue' in a for-loop body will duplicate the step statement
   * Assume the occurrences of "continue" and "break" have been verified
   *   to be inside loops during type-checking
   *)
  fun elim_for (s as A.Assign _) step_opts ext = s
    | elim_for (s as A.Exp _) step_opts ext = s
    | elim_for (A.Seq(ds,ss)) step_opts ext = A.Seq(ds,elim_fors ss step_opts ext)
    | elim_for (A.StmDecl d) step_opts ext = A.StmDecl d
    | elim_for (A.If(e,s1,s2)) step_opts ext =
        A.If(e, elim_for s1 step_opts ext, elim_for s2 step_opts ext)
    | elim_for (A.While(e, specs, s)) step_opts ext =
        A.While(e, specs, elim_for s (NONE::step_opts) ext)
    | elim_for (A.For(A.StmDecl(d), e, s2, invs, s3)) step_opts ext =
      let val s3' = elim_for s3 (SOME(s2)::step_opts) ext
      in
	  A.Seq([d], [A.While(e, invs, A.Seq(nil, [s3',s2]))])
      end
    | elim_for (A.For(s1, e, s2, invs, s3)) step_opts ext =
      let val s3' = elim_for s3 (SOME(s2)::step_opts) ext
      in
          A.Seq(nil, [s1, A.While(e, invs, A.Seq(nil, [s3', s2]))])
      end
    | elim_for (A.Continue) (NONE::step_opts) ext = A.Continue
    | elim_for (A.Continue) (SOME(s)::step_opts) ext = A.Seq(nil,[s, A.Continue])
    | elim_for (A.Break) (_::_) ext = A.Break
    | elim_for (s as A.Return _) step_opts ext = s
    | elim_for (s as A.Assert _) step_opts ext = s
    | elim_for (s as A.Error _) step_opts ext = s 
    | elim_for (s as A.Anno(specs)) step_opts ext = s
    | elim_for (A.Markeds(marked_stm)) step_opts ext = (* preserve marks *)
        A.Markeds(Mark.mark' (elim_for (Mark.data marked_stm) step_opts (Mark.ext marked_stm),
			      Mark.ext marked_stm))

  and elim_fors nil step_opts ext = nil
    | elim_fors (s::ss) step_opts ext =
        (elim_for s step_opts ext)::(elim_fors ss step_opts ext)

  fun elim_fors_fun (A.Function(g, tp, params, SOME(s), specs, is_extern, ext)) =
      A.Function(g, tp, params, SOME(elim_for s nil ext), specs, is_extern, ext)
    | elim_fors_fun (fdecl as A.Function(g, tp, params, NONE, specs, is_extern, ext)) =
      fdecl

  (*************************)
  (* Checking control flow *)
  (*************************)

  (* rc_stm s = true if every finite control flow path in s ends with 'return' or 'error' *)
  (* assumes for-loops have been eliminated *)
  fun rc_stm (A.Assign(oper_op, lv, e)) = false
    | rc_stm (A.Seq(ds,ss)) = rc_stms ss
    | rc_stm (A.Exp(e)) = false
    | rc_stm (A.If(e, s1, s2)) = rc_stm s1 andalso rc_stm s2
    | rc_stm (A.While(e, invs, s)) = false
    (* no A.For *)
    | rc_stm (A.Return(SOME(e))) = true
    | rc_stm (A.Return(NONE)) = false (* empty return not permitted *)
    | rc_stm (A.Assert _) = false
    | rc_stm (A.Error _) = true
    | rc_stm (A.Anno _) = false
    | rc_stm (A.Markeds(marked_stm)) =
        rc_stm (Mark.data marked_stm)

  and rc_stms nil = false
    | rc_stms (s::ss) =
        (* traverse from last to first for common case *)
        rc_stms ss orelse rc_stm s

  fun rc_fun (A.Function(f, rtp, params, SOME(s), specs, _, ext)) =
      (case rtp
	of A.Void => () (* no return statements required *)
	 | _ => if rc_stm s
		then ()
		else ( ErrorMsg.error ext 
                         ("function '" ^ Symbol.name f ^ "' does not end in a return statement")
		     ; raise ErrorMsg.Error ))
    | rc_fun (fdecl as A.Function _) = (* function declaration - nothing to check *)
      ()

  fun chk_fun_body (fdecl) =
      let val () = rt_fdecl fdecl (* check proper use of \length, \result, \old *)
	  val () = chk_fun fdecl (* type-check *)
	  val fdecl' = elim_fors_fun fdecl (* elim for loops to simplify control *)
	  val () = rc_fun fdecl' (* check valid returns *)
	  val () = lv_fun fdecl' (* check initialization of variables *)
      in
	  fdecl'
      end

  (* add ext to this function? *)
  fun typecheck_interpreter env stm =
      let
          val () = nr_stm stm NONE (* Check absense of returns *)
          val () = rt_stm stm NONE (* Check proper use of \length, etc. *)
          val () = chk_stm env stm Ast.Any false NONE (* Type check *)
          val stm' = elim_for stm nil NONE (* Eliminate for loops *)
      in 
          stm'
      end

  fun params_to_types (A.VarDecl(x, tp, e_opt, ext)::decls) = tp::params_to_types decls
    | params_to_types (nil) = nil

  (*******************************)
  (* Checking struct definitions *)
  (*******************************)

  (* chk_diff_fields f fields = (), raises Error if f is a field name in fields *)
  fun chk_diff_fields f nil = ()
    | chk_diff_fields f (A.Field(f',tp,ext)::fields) =
      (case Symbol.compare(f,f')
         of EQUAL => ( ErrorMsg.error ext "field name used twice"
		     ; raise ErrorMsg.Error )
          | _ => chk_diff_fields f fields)

  (* chk_struct_filds fields = (), raise Error if not well-formed *)
  fun chk_struct_fields nil = ()
    | chk_struct_fields (A.Field(f, tp, ext)::fields) =
	( chk_diff_fields f fields
	; chk_tp tp ext
	; chk_known_size tp ext
	; chk_struct_fields fields )

  (********************************)
  (* Checking global declarations *)
  (********************************)

  (* tc_gdecl gdecl is_library = gdecl'
   * Type-check a global declaration and return a modified declaration
   * where the is_library status of gdecl has been updated appropriately, and
   * other normalizations might take place (e.g., for-loop replaced by while-loop).
   * Raises Error if not well-typed (including other static semantics violations).
   *
   * Maintains the global table Symtab and struct table Structtab to detect
   * illegal double definitions or name clashes.
   *
   * Symtab maps id to most recent A.TypeDef or A.Function defn (if exists) or decl
   * Structtab maps sid to most recent A.Struct defn (if exists) or decl
   *)
  fun tc_gdecl (tdef as A.TypeDef(aid, tp, ext)) is_library =
      ( case Symtab.lookup aid
	 of NONE => ( chk_tp tp ext ; Symtab.bind(aid, tdef) )
	  | SOME(A.TypeDef(aid', tp', ext')) =>
		 ( ErrorMsg.error ext ("type name '" ^ Symbol.name aid ^ "' defined more than once\n"
				       ^ "previous definition at " ^ Mark.show (Option.valOf ext'))
		 ; raise ErrorMsg.Error )
          | SOME(A.Function(gid, _, _, _, _, _, ext')) =>
                 ( ErrorMsg.error ext ("type name '" ^ Symbol.name aid ^ "' already used as function name\n"
                                       ^ "function definition at " ^ Mark.show (Option.valOf ext'))
                 ; raise ErrorMsg.Error )
      ; tdef )
    | tc_gdecl (sdecl as A.Struct(sid, NONE, is_extern, ext)) is_library =
      ( case Structtab.lookup sid
	 of NONE => Structtab.bind (sid, sdecl)
	  | SOME _ => () (* declared or defined before; now declared is ok *)
      ; sdecl )
    | tc_gdecl (sdecl as A.Struct(sid, SOME(fields), _, ext)) is_library =
      (case Structtab.lookup sid
	of NONE => ( chk_struct_fields fields ;
		     Structtab.bind(sid, sdecl) )
	 | SOME(A.Struct(sid', NONE, is_extern', ext')) => (* previously declared *)
	   ( if (not is_library) andalso is_extern'
	     then ( ErrorMsg.error ext
		      ("'struct " ^ Symbol.name sid ^ "' declared in library cannot be defined\n"
		       ^ "library declaration at " ^ Mark.show(Option.valOf ext'))
		    ; raise ErrorMsg.Error )
	     else ()
	   ; chk_struct_fields fields
	   ; Structtab.bind(sid, sdecl) )
	 | SOME(A.Struct(sid', SOME _, _, ext')) => (* previously defined *)
	   ( ErrorMsg.error ext ("'struct " ^ Symbol.name sid ^ "' defined more than once\n"
				 ^ "previous definition at " ^ Mark.show(Option.valOf ext'))
	   ; raise ErrorMsg.Error )
     ; sdecl )
    | tc_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) is_library =
      (* function declaration, override is_extern with current context is_library *)
      let val fdecl = A.Function(g, rtp, params, NONE, specs, is_library, ext) 
	  val () = case Symtab.lookup g
		    of NONE => Symtab.bind (g, fdecl)
		     | SOME(A.Function(g', rtp', params', NONE, specs', is_extern', ext')) =>
		       (* already declared: check if types are compatible *)
		       ( chk_conv rtp rtp' ext
		         (fn () => "mismatching return types for multiple declarations of function '"
				   ^ Symbol.name g ^ "'")
		       ; chk_convs (params_to_types params) (params_to_types params') ext
			 (fn () => "mismatching parameter types for multiple declarations of function '"
				   ^ Symbol.name g ^ "'")
		       ; if is_extern'
			 then () (* leave the original library declaration in place *)
			 else Symtab.bind (g, fdecl) ) (* correct with subtyping? *)
		     | SOME(A.Function(g', rtp', params', SOME _, specs', _, ext')) =>
		       (* already defined: check if types are compatible, otherwise ignore *)
		       ( chk_conv rtp rtp' ext
			 (fn () => "mismatched return types for definition and declaration of function '"
				   ^ Symbol.name g ^ "'")
		       ; chk_convs (params_to_types params) (params_to_types params') ext
			 (fn () => "mismatched parameter types for multiple declarations of function '"
				   ^ Symbol.name g ^ "'")
		       (* ignore declaration after previous definition *)
                       (* correct with subtyping? *)
		       ; () )
		     | SOME(A.TypeDef(aid, tp, ext')) =>
		       ( ErrorMsg.error ext ("cannot use type name '" ^ Symbol.name aid ^ "' as function name")
		       ; raise ErrorMsg.Error )
      in
	  chk_fun_body fdecl
      end
    | tc_gdecl (A.Function(g, rtp, params, SOME(s), specs, _, ext)) is_library =
      (* function definition, override is_extern with current context is_library *)
      let val fdecl = A.Function(g, rtp, params, SOME(s), specs, is_library, ext)
	  (* remove from list of undefined, but used function symbols, because is now defined *)
	  val () = Symset.remove g handle NotFound => ();
	  val () = case Symtab.lookup g
		    of NONE => Symtab.bind (g, fdecl) (* bind first to allow recursion *)
		     | SOME(A.Function(g', rtp', params', NONE, specs', is_library', ext')) =>
		       (* previously declared *)
		       ( if (not is_library) andalso is_library'
			 then (* function previously declared in a library cannot be defined outside of it *)
			     ( ErrorMsg.error ext
			        ("cannot define function declared in a library\n"
				 ^ "previous declaration at " ^ Mark.show (Option.valOf ext'))
			     ; raise ErrorMsg.Error )
			 else ()
                       (* check compatibility of types *)
		       ; chk_conv rtp rtp' ext
		         (fn () => "mismatching return types for multiple declarations of function '"
				   ^ Symbol.name g ^ "'")
                       (* need to change order below if subtyping is introduced *)
		       ; chk_convs (params_to_types params) (params_to_types params') ext
			 (fn () => "mismatched parameter types for declaration and definition of function '"
				   ^ Symbol.name g ^ "'")
		       ; Symtab.bind (g, fdecl) )
		    | SOME(A.Function(g', rtp', params', SOME _, _, _, ext')) =>
		      ( ErrorMsg.error ext ("function '" ^ Symbol.name g ^ "' defined more than once\n"
					    ^ "previous definition at " ^ Mark.show (Option.valOf ext'))
		      ; raise ErrorMsg.Error )
		    | SOME(A.TypeDef(aid, tp, ext')) =>
		      ( ErrorMsg.error ext ("cannot define type name '" ^ Symbol.name aid ^ "' as function name")
		      ; raise ErrorMsg.Error )
      in
	  chk_fun_body fdecl
      end
    | tc_gdecl (gdecl as A.Pragma(A.Raw(pname, pargs), ext)) is_library =
      ( ErrorMsg.warn ext ("ignoring pragma " ^ pname)
      ; gdecl )
    | tc_gdecl (gdecl as A.Pragma(p, ext)) is_library =
      (* pragmas have already been checked or are to be ignored *)
      gdecl

  (* tc_gdecls gdecls is_library = gdecls'
   * type-check and transform gdecls, raise Error if not well-typed *)
  fun tc_gdecls nil is_library = nil
    | tc_gdecls (gdecl::gdecls) is_library =
      tc_gdecl gdecl is_library :: tc_gdecls gdecls is_library

  fun typecheck (gdecls, is_library) =
      let 
	  val gdecls' = tc_gdecls gdecls is_library
      in
	  gdecls' (* return rewritten program *)
      end

  fun symbol_names nil = ""
    | symbol_names (id::ids) =
        Symbol.name id ^ " " ^ symbol_names ids

  (* check_all_defined () = (), raises Error if not all used functions are defined.
   * Uses the global Symset to track function names that have been used, but
   * not yet defined.  Symset is created by the typechecker (functions tc_<cat>).
   *)
  fun check_all_defined () =
      let val undefineds = Symset.list ()
	  fun isNotLibrary (SOME(A.Function(_, _, _, _, _, false, _))) = true
	    | isNotLibrary _ = false
	  val missing = List.filter (isNotLibrary o Symtab.lookup) undefineds
      in
	  case missing
	   of (_ :: _) => ( ErrorMsg.error NONE ("undefined functions: " ^ symbol_names missing) ;
			    raise ErrorMsg.Error )
	    | nil => ()
      end

end
