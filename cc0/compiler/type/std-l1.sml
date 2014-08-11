structure StdL1 :> STD =
struct

structure A = Ast

fun spec_ext (A.Requires(_, ext)) = ext
  | spec_ext (A.Ensures(_, ext)) = ext
  | spec_ext (A.LoopInvariant(_, ext)) = ext
  | spec_ext (A.Assertion(_, ext)) = ext

fun legal_oper oper = case oper of
  (* A.SUB => false, check inline *)
    A.LOGNOT => false
  | A.COMPLEMENT => false
  | A.NEGATIVE => true
  | A.DEREF => false
  | A.TIMES => true | A.DIVIDEDBY => true | A.MODULO => true
  | A.PLUS => true | A.MINUS => true
  | A.SHIFTLEFT => false
  | A.SHIFTRIGHT => false
  | A.LESS => false | A.LEQ => false | A.GREATER => false | A.GEQ => false
  | A.EQ => false | A.NOTEQ => false
  | A.AND => false | A.XOR => false | A.OR => false
  | A.LOGAND => false | A.LOGOR => false
  (* A.COND => false, checked inline *)

fun chk_oper oper ext =
    if not (legal_oper oper)
    then ( ErrorMsg.error ext
           ("operator '" ^ A.Print.pp_oper oper ^ "' not supported in L1")
         ; raise ErrorMsg.Error )
    else ()

fun chk_tp (A.Int) ext = ()
  | chk_tp (tp) ext =
    ( ErrorMsg.error ext
      ("type '" ^ A.Print.pp_tp tp ^ "' not supported in L1")
    ; raise ErrorMsg.Error )

fun chk_exp (A.Var _) ext = ()
  | chk_exp (A.IntConst _) ext = ()
  | chk_exp (e as A.StringConst _) ext =
    ( ErrorMsg.error ext ("string constants not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (e as A.CharConst _) ext =
    ( ErrorMsg.error ext ("character constant not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (e as A.True) ext =
    ( ErrorMsg.error ext ("boolean constants not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (e as A.False) ext =
    ( ErrorMsg.error ext ("boolean constants not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (e as A.Null) ext =
    ( ErrorMsg.error ext ("null pointer not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (e as A.OpExp(A.SUB, _)) ext =
    ( ErrorMsg.error ext ("array access not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (e as A.OpExp(A.COND, _)) ext =
    ( ErrorMsg.error ext ("conditional expressions not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (A.OpExp(oper, es)) ext =
    ( chk_oper oper ext ; chk_exps es ext )
  | chk_exp (A.Select _) ext =
    ( ErrorMsg.error ext ("selecting struct components not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (A.FunCall _) ext =
    ( ErrorMsg.error ext ("function calls not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (A.Alloc _) ext =
    ( ErrorMsg.error ext ("cell allocation not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (A.AllocArray _) ext =
    ( ErrorMsg.error ext ("array allocation not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (A.Cast _) ext =
    ( ErrorMsg.error ext ("cast not supported in L1") ; raise ErrorMsg.Error )
  | chk_exp (A.Marked(marked_exp)) ext =
      chk_exp (Mark.data marked_exp) (Mark.ext marked_exp)
  | chk_exp e ext = (* impossible? *)
    ( ErrorMsg.error ext ("special identifiers \\result, \\length, \\old not supported in L1")
    ; raise ErrorMsg.Error )

and chk_exps es ext = List.app (fn e => chk_exp e ext) es

fun chk_stm (A.Assign(NONE, lv, e)) ext =
    ( chk_exp lv ext ; chk_exp e ext )
  | chk_stm (A.Assign(SOME(A.MINUS), lv, A.IntConst _)) ext =
    ( ErrorMsg.error ext
      ("statement <lv>-- not supported in L1")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Assign(SOME(A.PLUS), lv, A.IntConst _)) ext = (* should be impossible? *)
    ( ErrorMsg.error ext
      ("statement <lv>++ not supported in L1")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Assign(SOME(oper), lv, e)) ext =
    if not (legal_oper oper)
    then ( ErrorMsg.error ext
           ("assignment operator '" ^ A.Print.pp_oper oper ^ "' not supported in L1")
         ; raise ErrorMsg.Error )
    else ( chk_exp lv ext ; chk_exp e ext )
  | chk_stm (A.Exp(e)) ext =
    ( ErrorMsg.error ext
      ("expressions not supported as statements in L1")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Seq(ds, ss)) ext =
    ( List.app (fn d => chk_decl d) ds
    ; List.app (fn s => chk_stm s ext) ss )
  | chk_stm (A.StmDecl(d)) ext = chk_decl d
  | chk_stm (A.If(e, s1, s2)) ext =
    ( ErrorMsg.error ext ("conditionals not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.While(e, specs, s)) ext = 
    ( ErrorMsg.error ext ("while loops not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.For(s1, e2, s3, specs, s4)) ext =
    ( ErrorMsg.error ext ("for loops not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Continue) ext =
    ( ErrorMsg.error ext ("statement 'continue' not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Break) ext =
    ( ErrorMsg.error ext ("statement 'break' not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Return(NONE)) ext =
    ( ErrorMsg.error ext ("return with no value not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Return(SOME(e))) ext =
    ( chk_exp e ext )         
  | chk_stm (A.Assert(e, _)) ext =
    ( ErrorMsg.error ext ("assertion statements not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Error _) ext =
    ( ErrorMsg.error ext ("error statements not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Anno _) ext =
    ( ErrorMsg.error ext ("contract annotations not supported in L1") ; raise ErrorMsg.Error )
  | chk_stm (A.Markeds(marked_stm)) ext =
      chk_stm (Mark.data marked_stm) (Mark.ext marked_stm)

and chk_decl (A.VarDecl(id, tp, NONE, ext)) = chk_tp tp ext
  | chk_decl (A.VarDecl(id, tp, SOME(e), ext)) =
    ( chk_tp tp ext ; chk_exp e ext )

and chk_specs nil = ()
  | chk_specs (spec::_) =
    ( ErrorMsg.error (spec_ext spec) ("contract annotations not supported in L1") ; raise ErrorMsg.Error )

fun chk_gdecl (A.TypeDef(_, _, ext)) =
    ( ErrorMsg.error ext ("type definitions not supported in L1") ; raise ErrorMsg.Error )
  | chk_gdecl (A.Struct(_, _, _, ext)) =
    ( ErrorMsg.error ext ("structs not supported in L1") ; raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) =
    ( ErrorMsg.error ext ("function declarations not supported in L1") ; raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, _, ext)) =
    if Symbol.name g <> "main"
    then ( ErrorMsg.error ext ("only function 'main' may be defined in L1") ; raise ErrorMsg.Error )
    else ( chk_specs specs ; chk_stm s ext )
  | chk_gdecl (A.Pragma(_, ext)) =
    ( ErrorMsg.error ext ("compiler directives not supported in L1") ; raise ErrorMsg.Error )

fun check gdecls = List.app chk_gdecl gdecls

end
