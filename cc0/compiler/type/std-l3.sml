structure StdL3 :> STD =
struct

structure A = Ast

fun spec_ext (A.Requires(_, ext)) = ext
  | spec_ext (A.Ensures(_, ext)) = ext
  | spec_ext (A.LoopInvariant(_, ext)) = ext
  | spec_ext (A.Assertion(_, ext)) = ext

fun legal_oper oper = case oper of
  (* A.SUB => false, check inline *)
    A.LOGNOT => true           (* L2 *)
  | A.COMPLEMENT => true       (* L2 *)
  | A.NEGATIVE => true         (* L1 *)
  | A.DEREF => false
  | A.TIMES => true | A.DIVIDEDBY => true | A.MODULO => true (* L1 *)
  | A.PLUS => true | A.MINUS => true                         (* L1 *)
  | A.SHIFTLEFT => true                                      (* L2 *)
  | A.SHIFTRIGHT => true                                     (* L2 *)
  | A.LESS => true | A.LEQ => true | A.GREATER => true | A.GEQ => true (* L2 *)
  | A.EQ => true | A.NOTEQ => true (* L2 *)
  | A.AND => true | A.XOR => true | A.OR => true (* L2 *)
  | A.LOGAND => true | A.LOGOR => true           (* L2 *)
  | A.COND => true                               (* L2 *)

fun chk_oper oper ext =
    if not (legal_oper oper)
    then ( ErrorMsg.error ext
           ("operator '" ^ A.Print.pp_oper oper ^ "' not supported in L3")
         ; raise ErrorMsg.Error )
    else ()

fun chk_tp (A.Int) ext = ()     (* L1 *)
  | chk_tp (A.Bool) ext = ()    (* L2 *)
  | chk_tp (A.TypeName(a)) ext = () (* L3 *)
  | chk_tp (A.Void) ext = ()
  | chk_tp (tp) ext =
    ( ErrorMsg.error ext
      ("type '" ^ A.Print.pp_tp tp ^ "' not supported in L3")
    ; raise ErrorMsg.Error )

fun chk_exp (A.Var _) ext = ()  (* L1 *)
  | chk_exp (A.IntConst _) ext = () (* L1 *)
  | chk_exp (e as A.StringConst _) ext =
    ( ErrorMsg.error ext ("string constants not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (e as A.CharConst _) ext =
    ( ErrorMsg.error ext ("character constant not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (e as A.True) ext = () (* L2 *)
  | chk_exp (e as A.False) ext = () (* L2 *)
  | chk_exp (e as A.Null) ext =
    ( ErrorMsg.error ext ("null pointer not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (e as A.OpExp(A.SUB, _)) ext =
    ( ErrorMsg.error ext ("array access not supported in L3") ; raise ErrorMsg.Error )
  (* | chk_exp (e as A.OpExp(A.COND, _)) ext *)
  (* now allowed: fall through to next case *)
  (* L2 *)
  | chk_exp (A.OpExp(oper, es)) ext =
    ( chk_oper oper ext ; chk_exps es ext )
  | chk_exp (A.Select _) ext =
    ( ErrorMsg.error ext ("selecting struct components not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (A.FunCall(f,es)) ext = (* L3 *)
    ( chk_exps es ext )
  | chk_exp (A.Alloc _) ext =
    ( ErrorMsg.error ext ("cell allocation not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (A.AllocArray _) ext =
    ( ErrorMsg.error ext ("array allocation not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (A.Cast _) ext =
    ( ErrorMsg.error ext ("cast not supported in L3") ; raise ErrorMsg.Error )
  | chk_exp (A.Marked(marked_exp)) ext =
      chk_exp (Mark.data marked_exp) (Mark.ext marked_exp)
  | chk_exp e ext = (* impossible? *)
    ( ErrorMsg.error ext ("special identifiers \\result, \\length, \\old not supported in L3")
    ; raise ErrorMsg.Error )

and chk_exps es ext = List.app (fn e => chk_exp e ext) es

fun chk_stm (A.Assign(NONE, lv, e)) ext = (* L1 *)
    ( chk_exp lv ext ; chk_exp e ext )
  (* lv++; and lv--; allowed in L2 *)
  (*
  | chk_stm (A.Assign(SOME(A.MINUS), lv, A.IntConst _)) ext =
    ( ErrorMsg.error ext
      ("statement <lv>-- not supported in L1")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Assign(SOME(A.PLUS), lv, A.IntConst _)) ext = (* should be impossible? *)
    ( ErrorMsg.error ext
      ("statement <lv>++ not supported in L1")
    ; raise ErrorMsg.Error )
  *)
  | chk_stm (A.Assign(SOME(oper), lv, e)) ext =
    if not (legal_oper oper)    (* all opers allowed here should now be legal *)
    then ( ErrorMsg.error ext
           ("assignment operator '" ^ A.Print.pp_oper oper ^ "' not supported in L3")
         ; raise ErrorMsg.Error )
    else ( chk_exp lv ext ; chk_exp e ext )
  | chk_stm (A.Exp(e)) ext =
      chk_exp e ext
  | chk_stm (A.Seq(ds, ss)) ext = (* L1 *)
    ( List.app (fn d => chk_decl d) ds
    ; List.app (fn s => chk_stm s ext) ss )
  | chk_stm (A.StmDecl(d)) ext = chk_decl d
  | chk_stm (A.If(e, s1, s2)) ext = (* L2 *)
    ( chk_exp e ext ; chk_stm s1 ext ; chk_stm s2 ext )
  | chk_stm (A.While(e, specs, s)) ext = (* L2 *)
    (* specs = nil by invariant *)
    ( chk_exp e ext ; chk_specs specs ; chk_stm s ext )
  | chk_stm (A.For(s1, e2, s3, specs, s4)) ext = (* L2 *)
    (* specs = nil by invariant *)
    ( chk_stm s1 ext ; chk_exp e2 ext ; chk_stm s3 ext ; chk_specs specs ; chk_stm s4 ext )
  | chk_stm (A.Continue) ext =
    ( ErrorMsg.error ext ("statement 'continue' not supported in L3") ; raise ErrorMsg.Error )
  | chk_stm (A.Break) ext =
    ( ErrorMsg.error ext ("statement 'break' not supported in L3") ; raise ErrorMsg.Error )
  | chk_stm (A.Return(NONE)) ext = (* L3 *)
    ()
  | chk_stm (A.Return(SOME(e))) ext = (* L1 *)
    ( chk_exp e ext )
  | chk_stm (A.Assert(e, _)) ext =
    ( chk_exp e ext )           (* L3 *)
  | chk_stm (A.Error _) ext =
    ( ErrorMsg.error ext ("error statements not supported in L3") ; raise ErrorMsg.Error )
  | chk_stm (A.Anno _) ext =
    ( ErrorMsg.error ext ("contract annotations not supported in L3") ; raise ErrorMsg.Error )
  | chk_stm (A.Markeds(marked_stm)) ext =
      chk_stm (Mark.data marked_stm) (Mark.ext marked_stm)

and chk_decl (A.VarDecl(id, tp, NONE, ext)) = chk_tp tp ext
  | chk_decl (A.VarDecl(id, tp, SOME(e), ext)) =
    ( chk_tp tp ext ; chk_exp e ext )

and chk_specs nil = ()
  | chk_specs (spec::_) =
    ( ErrorMsg.error (spec_ext spec) ("contract annotations not supported in L3") ; raise ErrorMsg.Error )

fun chk_params nil = ()
  | chk_params (A.VarDecl(id, tp, NONE, ext)::params) =
    ( chk_tp tp ext ; chk_params params )

fun chk_gdecl (A.TypeDef(a, tp, ext)) = (* L3 *)
    ( chk_tp tp ext )
  | chk_gdecl (A.Struct(_, _, _, ext)) =
    ( ErrorMsg.error ext ("structs not supported in L3") ; raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) = (* L3 *)
    (* internal or external allowed *)
    ( chk_tp rtp ext ; chk_params params )
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, true, ext)) =
    (* external function definitions not allowed *) (* L3 *)
    ( ErrorMsg.error ext ("external functions may only be declared, not defined in L3") ;
      raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, false, ext)) =
    (* not external *) (* L3 *)
    ( chk_tp rtp ext ; chk_params params
    ; chk_specs specs ; chk_stm s ext )
  | chk_gdecl (A.Pragma(_, ext)) =
    ( ErrorMsg.error ext ("compiler directives not supported in L3") ; raise ErrorMsg.Error )

fun check gdecls = List.app chk_gdecl gdecls

end
