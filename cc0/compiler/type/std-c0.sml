structure StdC0 :> STD =
struct

structure A = Ast

fun chk_stm (A.Markeds(marked_stm)) ext =
      chk_stm (Mark.data marked_stm) (Mark.ext marked_stm)
  | chk_stm (A.Seq(ds, ss)) ext = List.app (fn s => chk_stm s ext) ss
  | chk_stm (A.If(e, s1, s2)) ext = ( chk_stm s1 ext ; chk_stm s2 ext )
  | chk_stm (A.While(e, specs, s)) ext = chk_stm s ext
  | chk_stm (A.For(s1, e2, s3, specs, s4)) ext =
    ( chk_stm s1 ext ; chk_stm s3 ext ; chk_stm s4 ext )
  | chk_stm (A.Continue) ext =
    ( ErrorMsg.error ext
                     ("statement 'continue' unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Break) ext =
    ( ErrorMsg.error ext
                     ("statement 'break' unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_stm s ext = (* A.Assign, A.Exp, A.StmDecl, A.Return, A.Assert, A.Error, A.Anno *)
    ()

fun chk_gdecl (A.TypeDef _) = ()
  | chk_gdecl (A.Struct _) = ()
  | chk_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) = ()
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, _, ext)) =
      chk_stm s ext
  | chk_gdecl (A.Pragma _) = ()

fun check gdecls = List.app chk_gdecl gdecls

end
