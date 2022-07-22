signature TRANSLATE =
sig
    val translateExp : Ast.exp -> VAst.Exp
    val translateStm : Ast.stm -> VAst.stm
    val translateVardecl : Ast.vardecl -> VAst.vardecl
    val translateTp : Ast.tp -> VAst.tp
    val translateGdecl : Ast.gdecl -> VAst.gdecl
    val translateField : Ast.field -> VAst.field
    val translateSpec : Ast.spec -> VAst.spec
    val translatePragma : Ast.pragma -> VAst.pragma
    val translateProgram : Ast.program -> VAst.program
end

structure Translate :> TRANSLATE =
struct
    fun translateExp exp =
        case exp of
            Ast.Var v => VAst.SVar (v, version)
          | Ast.IntConst n => VAst.IntConst n
          | Ast.StringConst s => VAst.StringConst s
          | Ast.CharConst c => VAst.CharConst c
          | Ast.True => VAst.True
          | Ast.False => VAst.False
          | Ast.Null => VAst.Null
          | Ast.OpExp (oper, el) => VAst.OpExp (oper, map translateExp el)
          | Ast.Select(e, f) => VAst.Select (translateExp e, f)
          | Ast.FunCall (f, el) => VAst.FunCall (f, map translateExp el)
          | Ast.AddrOf (f) => VAst.AddrOf (f)
          | Ast.Invoke (e, el) => VAst.Invoke (translateExp e, map translateExp el)
          | Ast.Alloc(tp) => VAst.Alloc (translateTp tp)
          | Ast.AllocArray(tp, e) => VAst.AllocArray (translateTp tp, translateExp e)
          | Ast.Cast(tp, e) => VAst.Cast (translateTp tp, translateExp e)
          | Ast.Result => VAst.Result
          | Ast.Length e => VAst.Length (translateExp e)
          | Ast.Hastag(tp, e) => VAst.Hastag (translateTp tp, translateExp e)
          | Ast.Marked m => VAst.Marked m
    
          
    and translateStm stm =
        case stm of
            Ast.Assign (oper, lv, e) => VAst.Assign (oper, translateExp lv, translateExp e)
          | Ast.Exp (e) => VAst.Exp (translateExp e)
          | Ast.Seq (vlist, slist) => VAst.Seq (map translateVardecl vlist, map translateStm slist)
          | Ast.StmDecl (decl) => VAst.StmDecl (translateVardecl decl)
          | Ast.If (e, strue, sfalse) => VAst.If (translateExp e, translateStm strue, translateStm sfalse)
          | Ast.While (e, invs, body) => VAst.While (translateExp e, map translateSpec invs, translateStm body)
          | Ast.For () => 
          
          
end

