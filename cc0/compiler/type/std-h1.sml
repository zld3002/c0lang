structure StdH1 :> STD =
struct

structure A = Ast

fun chk_gdecl (A.Struct(s, NONE, _, ext)) = ()
  | chk_gdecl (A.Struct(s, SOME(fields), _, ext)) = ()
  | chk_gdecl (A.TypeDef(a, tp, ext)) = ()
  | chk_gdecl (A.FunTypeDef(fid, rtp, params, specs, ext)) = ()
  | chk_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) =
    ( ErrorMsg.error ext ("function definitions unsupported in language standard 'h1'")
    ; raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, _, ext)) = ()
  | chk_gdecl (A.Pragma _) = ()

fun check gdecls = List.app chk_gdecl gdecls

end
