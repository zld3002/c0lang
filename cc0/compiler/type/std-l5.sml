structure StdL5 :> STD =
struct

structure A = Ast

(* all types and expressions allowed as of L5 *)

fun chk_stm (A.Assign(NONE, lv, e)) ext = (* L1 *)
    ()
  (* lv++; and lv--; allowed as of L2 *)
  | chk_stm (A.Assign(SOME(oper), lv, e)) ext =
    ()
  | chk_stm (A.Exp(e)) ext =
    ()
  | chk_stm (A.Seq(ds, ss)) ext = (* L1 *)
    ( List.app (fn s => chk_stm s ext) ss )
  | chk_stm (A.StmDecl(d)) ext = ()
  | chk_stm (A.If(e, s1, s2)) ext = (* L2 *)
    ( chk_stm s1 ext ; chk_stm s2 ext )
  | chk_stm (A.While(e, specs, s)) ext = (* L2 *)
    (* specs = nil by invariant *)
    ( chk_stm s ext )
  | chk_stm (A.For(s1, e2, s3, specs, s4)) ext = (* L2 *)
    (* specs = nil by invariant *)
    ( chk_stm s1 ext ; chk_stm s3 ext ; chk_stm s4 ext )
  | chk_stm (A.Continue) ext =
    ( ErrorMsg.error ext ("statement 'continue' not supported in L5") ; raise ErrorMsg.Error )
  | chk_stm (A.Break) ext =
    ( ErrorMsg.error ext ("statement 'break' not supported in L5") ; raise ErrorMsg.Error )
  | chk_stm (A.Return(NONE)) ext = (* L3 *)
    ()
  | chk_stm (A.Return(SOME(e))) ext = (* L1 *)
    ()
  | chk_stm (A.Assert(e, _)) ext =
    ()           (* L3 *)
  | chk_stm (A.Error _) ext = (* L5 *)
    ( ErrorMsg.error ext ("statement 'error(msg)' not supported in L5") ; raise ErrorMsg.Error )
  | chk_stm (A.Anno _) ext = (* L5 *)
    (* ignoring //@assert contract annotations *)
    ()
  | chk_stm (A.Markeds(marked_stm)) ext =
      chk_stm (Mark.data marked_stm) (Mark.ext marked_stm)

fun chk_gdecl (A.TypeDef(a, tp, ext)) = (* L3 *)
    ()
  | chk_gdecl (A.FunTypeDef(fid, rtp, params, specs, ext)) = (* L5 *)
    (* specs = nil by invariant *)
    ()
  | chk_gdecl (A.Struct(s, NONE, _, ext)) = (* L4 *)
    ()
  | chk_gdecl (A.Struct(s, SOME(fields), _, ext)) = (* L4 *)
    ()
  | chk_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) = (* L3 *)
    (* internal or external allowed *)
    ()
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, true, ext)) =
    (* external function definitions not allowed *) (* L3 *)
    ( ErrorMsg.error ext ("external functions may only be declared, not defined in L5") ;
      raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, false, ext)) =
    (* not external *) (* L3 *)
    ( chk_stm s ext )
  | chk_gdecl (A.Pragma(_, ext)) =
    ( ErrorMsg.error ext ("compiler directives not supported in L5") ; raise ErrorMsg.Error )

fun check gdecls = List.app chk_gdecl gdecls

end
