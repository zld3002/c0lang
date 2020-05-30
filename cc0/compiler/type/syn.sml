(* C0 Compiler
 * Calculating types of well-typed expressions
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature SYN =
sig
    val syn_exp : Ast.tp Symbol.table -> Ast.exp -> Ast.tp
    val syn_exp_expd : Ast.tp Symbol.table -> Ast.exp -> Ast.tp
    val syn_decls : Ast.tp Symbol.table -> Ast.vardecl list -> Ast.tp Symbol.table
    val expand_def : Ast.tp -> Ast.tp
    val expand_fdef : Ast.tp -> Ast.tp (* arg must be function type or type name *)
    val expand_all : Ast.tp -> Ast.tp
    val lub : Ast.tp -> Ast.tp -> Ast.tp

    (* creating new temporary variable declarations, unitialized or initialized *)
    val new_tmp : Ast.tp -> Mark.ext option -> Ast.vardecl * Ast.exp
    val new_tmp_init : Ast.tp * Ast.exp -> Mark.ext option -> Ast.vardecl * Ast.exp
end

structure Syn :> SYN =
struct

  structure A = Ast

  (* should this use Symtab instead of Typetab, like typechecker.sml? *)
  (* replace by the version below *)
  (* Aug 14, 2014 -fp *)
  (*
  fun tp_expand (t) =
      case Typetab.lookup t
       of SOME(tp, ext) => tp
  *)

  fun tp_expand (aid) = case Symtab.lookup aid of
      SOME(A.TypeDef(aid, tp, ext)) => tp

  (* expand_def tp = tp', expand possible top-level type definitions *)
  (* do not expand function type definitions *)
  fun expand_def (A.TypeName(t)) = expand_def (tp_expand t)
    | expand_def (tp) = tp

  fun expand_fdef (A.FunTypeName(fid)) =
      ( case Symtab.lookup fid
         of SOME(A.FunTypeDef(fid', rtp, params, specs, ext)) =>
            A.FunType(rtp, params)
          (* should be only possibility *)
      )
    | expand_fdef (A.TypeName(aid)) = expand_fdef (tp_expand aid)
    | expand_fdef (tp as A.FunType _) = tp

  fun fun_type g =
      (case Symtab.lookup g
        of SOME(A.Function(g', rtp, params, _, _, _, _)) =>
           A.FunType(rtp, params))

  (* expand_all tp = tp', expand possible embedded type definitions *)
  fun expand_all (tp as A.Int) = tp
    | expand_all (tp as A.Bool) = tp
    | expand_all (tp as A.String) = tp
    | expand_all (tp as A.Char) = tp
    | expand_all (A.Pointer(tp)) = A.Pointer(expand_all tp)
    | expand_all (A.Array(tp)) = A.Array(expand_all tp)
    | expand_all (tp as A.StructName(s)) = tp
    | expand_all (A.TypeName(t)) = expand_all (tp_expand t)
    | expand_all (tp as A.FunTypeName _) = tp
    | expand_all (tp as A.FunType _) = tp (* possible? *)
    | expand_all (tp as A.Void) = tp
    | expand_all (tp as A.Any) = A.Any (* possible for statement NULL; *)

  (* lub tp1 tp2, least upper bound of two types (used in conditionals) *)
  (* assume that lub exists, since it is only applied to well-typed conditionals *)
  fun lub (A.Pointer(A.Any)) (A.Pointer(tp)) = A.Pointer(tp)
    | lub (A.Pointer(tp)) (A.Pointer(A.Any)) = A.Pointer(tp)
    | lub (A.TypeName(t1)) tp2 = lub (tp_expand t1) tp2
    | lub tp1 (A.TypeName(t2)) = lub tp1 (tp_expand t2)
    | lub A.Any tp2 = tp2
    | lub tp1 A.Any = tp1
    | lub (A.Pointer(tp1)) (A.Pointer(tp2)) = (* to access function types *)
        A.Pointer(lub tp1 tp2)
    (* lub on function pointers picks nominal alternative *)
    | lub (tp1 as A.FunType _) (tp2 as A.FunTypeName _) = tp2
    | lub (tp1 as A.FunTypeName _) (tp2 as A.FunType _) = tp1
    | lub tp1 tp2 = tp1  (* must be equal *)

  (* syn_var env id = tp, where env |- id : tp *)
  fun syn_var env id =
      case Symbol.look env id
         of SOME(tp) => tp
          | NONE => raise Fail ("symbol " ^ Symbol.name id ^ " not found")

  (* syn_field fields f = tp, where f : tp in fields *)
  fun syn_field (A.Field(f',tp,_)::fields) f =
      (case Symbol.compare(f',f)
        of EQUAL => tp
         | _ => syn_field fields f)

  (* syn_exp env e = tp, where env |- e : tp *)
  fun syn_exp env (A.Var(id)) = syn_var env id
    | syn_exp env (A.IntConst(w)) = A.Int
    | syn_exp env (A.StringConst(s)) = A.String
    | syn_exp env (A.CharConst(c)) = A.Char
    | syn_exp env (A.True) = A.Bool
    | syn_exp env (A.False) = A.Bool
    | syn_exp env (A.Null) = A.Pointer(A.Any)
    | syn_exp env (A.OpExp(A.SUB, [e1,e2])) =
      (case (syn_exp_expd env e1)
         of A.Array(tp) => tp)
    | syn_exp env (A.OpExp(A.DEREF, [e1])) =
      (case (syn_exp_expd env e1)
         of A.Pointer(tp) => tp)
    | syn_exp env (A.OpExp(A.EQ, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.NOTEQ, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.LOGNOT, [e])) = A.Bool
    | syn_exp env (A.OpExp(A.LESS, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.LEQ, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.GREATER, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.GEQ, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.LOGAND, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.LOGOR, [e1,e2])) = A.Bool
    | syn_exp env (A.OpExp(A.COND, [e1, e2, e3])) =
       lub (syn_exp env e2) (syn_exp env e3)
    | syn_exp env (A.OpExp(oper,es)) =
      (* all remaining operators are on integers only *)
        A.Int
    | syn_exp env (A.FunCall(g, es)) =
      (case Symtab.lookup g
         of SOME(A.Function(g', rtp, params, _, _, _, _)) => rtp)
    | syn_exp env (A.AddrOf(g)) =
        A.Pointer(fun_type g)
    | syn_exp env (A.Invoke(e, es)) =
      (case expand_fdef (syn_exp env e)
        of A.FunType(rtp, params) => rtp )
    | syn_exp env (A.Select(e,f)) =
      (case (syn_exp_expd env e)
        of A.StructName(s) =>
           (case Structtab.lookup s
             of SOME(A.Struct(s', SOME(fields), _, _)) => syn_field fields f))
    | syn_exp env (A.Alloc(tp)) = A.Pointer(tp)
    | syn_exp env (A.AllocArray(tp,e)) = A.Array(tp)
    | syn_exp env (A.Cast(tp,e)) = tp
    | syn_exp env (A.Result) = syn_var env (Symbol.symbol "\\result") (* ? Aug 18, 2014, -fp *)
    | syn_exp env (A.Length(e)) = A.Int
    | syn_exp env (A.Hastag(tp,e)) = A.Bool
    | syn_exp env (A.Marked(marked_exp)) =
        syn_exp env (Mark.data marked_exp)

  and syn_exp_expd env e = expand_def (syn_exp env e)

  and syn_decl env (A.VarDecl(id, tp, _, ext)) =
      Symbol.bind env (id, tp)

  and syn_decls env nil = env
    | syn_decls env (A.VarDecl(id, tp, _, ext)::decls) =
      syn_decls (Symbol.bind env (id, tp)) decls

  (* workaround for bug where typedef scope is violated,
     reported Feb 25, 2011 by wjl.  Should functions
     always be versioned as for contracts? -fp
  *)
  val syn_exp = fn env => fn e => expand_all (syn_exp env e)
  val syn_exp_expd = syn_exp

  local 
      val next = ref 0
      fun next_t () =
          let val _ = next := !next+1
          (* create new internal symbol *)
          in Symbol.new ("_tmp_" ^ Int.toString (!next)) end
  in
    fun new_tmp (tp) ext =
        let val t = next_t ()
        in (A.VarDecl(t, tp, NONE, ext), A.Var(t)) end

    fun new_tmp_init (tp, e) ext =
        let val t = next_t ()
        in (A.VarDecl(t, tp, SOME(e), ext), A.Var(t)) end
  end

end
