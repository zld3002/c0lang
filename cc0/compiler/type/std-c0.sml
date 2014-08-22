structure StdC0 :> STD =
struct

structure A = Ast

fun chk_tp tp ext = case tp of
    A.Int => ()
  | A.Bool => ()
  | A.String => ()
  | A.Char => ()
  | A.Pointer(A.Void) =>
    (* Type name cannot alias 'void', so pattern match is sufficient *)
    ( ErrorMsg.error ext ("type 'void*' unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | A.Pointer(tp') => chk_tp tp' ext
  | A.Array(tp') => chk_tp tp' ext
  | A.StructName _ => ()
  | A.TypeName _ => () (* definition check elsewhere *)
  | A.Void => ()
  (* Impossible *)
  (* | A.FunType *) (* Impossible, since address-of '&g' is disallowed *)
  (* | A.FunTypeName *) (* Impossible, since A.FunTypeDef is disallowed *)

fun chk_exp (A.Var _) ext = ()
  | chk_exp (A.IntConst _) ext = ()
  | chk_exp (A.StringConst _) ext = ()
  | chk_exp (A.CharConst _) ext = ()
  | chk_exp (A.True) ext = ()
  | chk_exp (A.False) ext = ()
  | chk_exp (A.Null) ext = ()
  | chk_exp (A.OpExp(opr, es)) ext = List.app (fn e => chk_exp e ext) es
  | chk_exp (A.Select(e, f)) ext = chk_exp e ext
  | chk_exp (A.FunCall(g, es)) ext = List.app (fn e => chk_exp e ext) es
  | chk_exp (A.AddrOf(g)) ext =
    ( ErrorMsg.error ext ("function pointers unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_exp (A.Invoke(e, es)) ext =
    ( ErrorMsg.error ext ("function pointers unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_exp (A.Alloc(tp)) ext = ()
  | chk_exp (A.AllocArray(tp, e)) ext = chk_exp e ext
  | chk_exp (A.Cast(tp, e)) ext =
    ( ErrorMsg.error ext ("casting unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_exp (A.Result) ext = ()
  | chk_exp (A.Length(e)) ext = chk_exp e ext
  | chk_exp (A.Hastag(tp,e)) ext =
    ( ErrorMsg.error ext ("casting unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_exp (A.Marked(marked_exp)) ext =
      chk_exp (Mark.data marked_exp) (Mark.ext marked_exp)

fun chk_spec (A.Requires(e, ext)) = chk_exp e ext
  | chk_spec (A.Ensures(e, ext)) = chk_exp e ext
  | chk_spec (A.LoopInvariant(e, ext)) = chk_exp e ext
  | chk_spec (A.Assertion(e, ext)) = chk_exp e ext

fun chk_specs specs = List.app chk_spec specs

fun chk_decl (A.VarDecl(id, tp, NONE, ext)) = chk_tp tp ext
  | chk_decl (A.VarDecl(id, tp, SOME(e), ext)) =
    ( chk_tp tp ext ; chk_exp e ext )
fun chk_decls ds = List.app chk_decl ds

fun chk_stm (A.Assign(_, e1, e2)) ext =
    ( chk_exp e1 ext ; chk_exp e2 ext )
  | chk_stm (A.Exp(e)) ext = chk_exp e ext
  | chk_stm (A.Seq(ds, ss)) ext = 
    ( chk_decls ds ; List.app (fn s => chk_stm s ext) ss )
  | chk_stm (A.StmDecl(d)) ext = chk_decl d
  | chk_stm (A.If(e, s1, s2)) ext =
    ( chk_exp e ext ; chk_stm s1 ext ; chk_stm s2 ext )
  | chk_stm (A.While(e, specs, s)) ext =
    ( chk_exp e ext ; chk_specs specs ; chk_stm s ext )
  | chk_stm (A.For(s1, e2, s3, specs, s4)) ext =
    ( chk_stm s1 ext ; chk_exp e2 ext ; chk_stm s3 ext
    ; chk_specs specs ; chk_stm s4 ext )
  | chk_stm (A.Continue) ext =
    ( ErrorMsg.error ext ("statement 'continue' unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Break) ext =
    ( ErrorMsg.error ext ("statement 'break' unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_stm (A.Return(NONE)) ext = ()
  | chk_stm (A.Return(SOME(e))) ext = chk_exp e ext
  | chk_stm (A.Assert(e, _)) ext = chk_exp e ext
  | chk_stm (A.Error(e)) ext = chk_exp e ext
  | chk_stm (A.Anno(specs)) ext = chk_specs specs
  | chk_stm (A.Markeds(marked_stm)) ext =
      chk_stm (Mark.data marked_stm) (Mark.ext marked_stm)

fun chk_field (A.Field(f, tp, ext)) = chk_tp tp ext

fun chk_gdecl (A.Struct(s, NONE, _, ext)) = ()
  | chk_gdecl (A.Struct(s, SOME(fields), _, ext)) =
      List.app (fn field => chk_field field) fields
  | chk_gdecl (A.TypeDef(a, tp, ext)) = chk_tp tp ext
  | chk_gdecl (A.FunTypeDef(fid, rtp, params, specs, ext)) =
    ( ErrorMsg.error ext ("function type definitions unsupported in language standard 'c0'")
    ; raise ErrorMsg.Error )
  | chk_gdecl (A.Function(g, rtp, params, NONE, specs, _, ext)) =
      ( chk_tp rtp ext ; chk_decls params ; chk_specs specs )
  | chk_gdecl (A.Function(g, rtp, params, SOME(s), specs, _, ext)) =
      ( chk_tp rtp ext ; chk_decls params ; chk_stm s ext ; chk_specs specs )
  | chk_gdecl (A.Pragma _) = ()

fun check gdecls = List.app chk_gdecl gdecls

end
