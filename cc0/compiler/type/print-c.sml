(* C0 Compiler
 * Printing to C
 * Author: Frank Pfenning <fp@cs.cmu.edu>
 *
 *)

signature PRINT =
sig
    val pp_program : Ast.program -> string
end

structure PrintC =
struct
  structure A = Ast

   fun extend_env env (A.VarDecl(id, tp, _, ext)::ds) =
         extend_env (Symbol.bind env (id, tp)) ds
     | extend_env env nil = env

   fun iso_exp env (e as A.Var(id)) = ([], [], e)
     | iso_exp env (e as A.IntConst(w)) = ([], [], e)
     | iso_exp env (e as A.StringConst(s)) = ([], [], e)
     | iso_exp env (e as A.CharConst(c)) = ([], [], e)
     | iso_exp env (e as A.True) = ([], [], e)
     | iso_exp env (e as A.False) = ([], [], e)
     | iso_exp env (e as A.Null) = ([], [], e)
     | iso_exp env (e as A.OpExp(A.SUB, [e1, e2])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (ds2, ss2, p2) = iso_exp env e2
	   val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in
	   (ds1 @ ds2 @ [d],
	    ss1 @ ss2 @ [A.Assign(NONE, t, A.OpExp(A.SUB, [p1, p2]))],
	    t)
       end
     | iso_exp env (e as A.OpExp(A.DEREF, [e1])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in
	   (ds1 @ [d], ss1 @ [A.Assign(NONE, t, A.OpExp(A.DEREF, [p1]))], t)
       end
     | iso_exp env (e as A.OpExp(A.DIVIDEDBY, [e1,e2])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (ds2, ss2, p2) = iso_exp env e2
	   val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in
	   (ds1 @ ds2 @ [d], 
	    ss1 @ ss2 @ [A.Assign(NONE, t, A.OpExp(A.DIVIDEDBY, [p1, p2]))],
	    t)
       end
     | iso_exp env (e as A.OpExp(A.MODULO, [e1,e2])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (ds2, ss2, p2) = iso_exp env e2
	   val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in
	   (ds1 @ ds2 @ [d],
	    ss1 @ ss2 @ [A.Assign(NONE, t, A.OpExp(A.MODULO, [p1, p2]))],
	    t)
       end
     (* A.SHIFTLEFT and A.SHIFTRIGHT translate to function calls, but these are pure *)
     | iso_exp env (A.OpExp(A.LOGAND, [e1, e2])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (ds2, ss2, p2) = iso_exp env e2
       in
	   (ds1 @ ds2, ss1 @ [A.If(p1, A.Seq(nil, ss2), A.Seq(nil, []))], A.OpExp(A.LOGAND, [p1,p2]))
       end 
     | iso_exp env (A.OpExp(A.LOGOR, [e1, e2])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (ds2, ss2, p2) = iso_exp env e2
       in
	   (ds1 @ ds2, ss1 @ [A.If(p1, A.Seq(nil,[]), A.Seq(nil,ss2))], A.OpExp(A.LOGOR, [p1, p2]))
       end 
     | iso_exp env (A.OpExp(A.COND, [e1, e2, e3])) =
       let val (ds1, ss1, p1) = iso_exp env e1
           val (ds2, ss2, p2) = iso_exp env e2
           val (ds3, ss3, p3) = iso_exp env e3
        in
	   (ds1 @ ds2 @ ds3, ss1 @ [A.If(p1, A.Seq(nil, ss2), A.Seq(nil, ss3))], A.OpExp(A.COND, [p1, p2, p3]))
       end
     | iso_exp env (A.OpExp(oper, [e1])) =
       let val (ds1, ss1, p1) = iso_exp env e1
       in (ds1, ss1, A.OpExp(oper, [p1])) end
     | iso_exp env (A.OpExp(oper, [e1,e2])) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (ds2, ss2, p2) = iso_exp env e2
       in (ds1 @ ds2, ss1 @ ss2, A.OpExp(oper, [p1, p2])) end
     | iso_exp env (e as A.Select(e1, f)) =
       (* e1 could have large type; isolate as lval *)
       (* iso_select env (A.Select(e1, f)) *)
       let val (ds1, ss1, p1) = iso_lv env e1
           val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
        in
	   (ds1 @ [d], ss1 @ [A.Assign(NONE, t, A.Select(p1, f))], t)
       end
     | iso_exp env (e as A.FunCall(g, es)) =
       let val (ds, ss, ps) = iso_exps env es
	   val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in (ds @ [d],
	   ss @ [A.Assign(NONE, t, A.FunCall(g, ps))],
	   t)
       end
     | iso_exp env (e as A.Alloc(tp)) =
       let val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in ([d], [A.Assign(NONE, t, A.Alloc(tp))], t) end
     | iso_exp env (e as A.AllocArray(tp, e1)) =
       let val (ds1, ss1, p1) = iso_exp env e1
	   val (d,t) = Syn.new_tmp(Syn.syn_exp env e)
       in (ds1 @ [d], ss1 @ [A.Assign(NONE, t, A.AllocArray(tp, p1))], t) end
     | iso_exp env (e as A.Result) = ([], [], e)
     | iso_exp env (A.Length(e1)) =
       (* \length(p1) has no effect *)
       let val (ds1, ss1, p1) = iso_exp env e1
       in (ds1, ss1, A.Length(p1)) end
     | iso_exp env (e as A.Old(e1)) =
       (* \old(e1) is not executed as given; leave alone for now *)
         ([], [], e)
     | iso_exp env (A.Marked(marked_exp)) =
         iso_exp env (Mark.data marked_exp)

    and iso_exps env nil = ([], [], [])
      | iso_exps env (e::es) =
	let val (ds1, ss1, p) = iso_exp env e
	    val (ds2, ss2, ps) = iso_exps env es
	in
	    (ds1 @ ds2, ss1 @ ss2, p::ps)
	end

    and iso_lv env (e as A.Var(x)) = ([], [], e)
      | iso_lv env (A.OpExp(A.SUB, [lv1, e2])) =
	let val (ds1, ss1, lv1') = iso_exp env lv1 (* Dec 2010, -fp *)
	    val (ds2, ss2, p2) = iso_exp env e2
	in
	    (ds1 @ ds2, ss1 @ ss2, A.OpExp(A.SUB, [lv1', p2]))
	end
      | iso_lv env (A.OpExp(A.DEREF, [lv1])) =
        (* e1 has small type t*; isolate as an expression *)
	let val (ds1, ss1, lv1') = iso_exp env lv1 (* Dec 2010, -fp *)
	in (ds1, ss1, A.OpExp(A.DEREF, [lv1'])) end
      | iso_lv env (A.Select(lv1, f2)) =
        (* lv1 could have large type; must isolate as an lval *)
	(* iso_select env (A.Select(e1, f2)) *)
	let val (ds1, ss1, lv1') = iso_lv env lv1
	in (ds1, ss1, A.Select(lv1', f2)) end
      | iso_lv env (A.Marked(marked_exp)) =
	  iso_lv env (Mark.data marked_exp)
      | iso_lv env (e) =
        (* any other form of expression has small type *)
	(* this case is necessary for expressions such as g()->f *)
	iso_exp env e

    fun iso_stm env (A.Assign(oper_opt, lv, e)) =
	let val (ds1, ss1, lv1) = iso_lv env lv
	in
	    iso_assign env oper_opt (ds1, ss1, lv1) e
	end
      | iso_stm env (A.Exp(e)) =
	(case Syn.syn_exp_expd env e
	  of A.Void =>
	     (* top level procedure call returning void *)
	     (* treat specially because we cannot bind a temporary *)
	     iso_funcall env e
	   | _ => let val (ds, ss, p) = iso_exp env e
		  in
		      (ds, ss @ [A.Exp(p)])
		  end )
      | iso_stm env (A.Seq(ds, ss)) =
	let val (ds1, ss1, env') = iso_decls env ds
	    val (ds2, ss2) = iso_stms env' ss
	in
	    ([], [A.Seq(ds1 @ ds2, ss1 @ ss2)])
	end
      | iso_stm env (A.StmDecl(d)) =
          iso_stm env (A.Seq([d], []))
      | iso_stm env (A.If(e, s1, s2)) =
	let val (ds, ss, p) = iso_exp env e
	    val (ds1, ss1) = iso_stm env s1
	    val (ds2, ss2) = iso_stm env s2
	in
	    (ds, ss @ [A.If(p, A.Seq(ds1,ss1), A.Seq(ds2,ss2))])
	end 
      | iso_stm env (A.While(e1, _, s2)) =
	let val (ds1, ss1, p1) = iso_exp env e1
	    val (ds2, ss2) = iso_stm env s2
            (* ss1 must be executed before the loop
             * and just before testing the condition
	     * again, which could happen at the end
             * of the loop body, or after a continue
             * encode this as a stylistic "for" loop
             * with identical init and step
             *)
	    val s1 = A.Seq([],ss1)
	in
	    (ds1, [A.For(s1, p1, s1, nil, A.Seq(ds2, ss2))])
	end 
      | iso_stm env (A.Continue) = ([], [A.Continue])
      | iso_stm env (A.Break) = ([], [A.Break])
      | iso_stm env (A.Return(SOME(e))) =
	let val (ds, ss, p) = iso_exp env e
	in
	    (ds, ss @ [A.Return(SOME(p))])
	end 
      | iso_stm env (A.Return(NONE)) = ([], [A.Return(NONE)])
      | iso_stm env (A.Assert(e1, e2s)) =
	let val (ds1, ss1, p1) = iso_exp env e1
	    val (ds2, ss2, p2s) = iso_exps env e2s
	in
	    (ds1 @ ds2, ss1 @ ss2 @ [A.Assert(p1, p2s)])
	end
      | iso_stm env (A.Anno(specs)) = (* ignore specs here *)
	  ([], [])
      | iso_stm env (A.Markeds(marked_stm)) =
	  iso_stm env (Mark.data marked_stm)

    and iso_stms env nil = (nil, nil)
      | iso_stms env (s::ss) =
	let val (ds1, ss1) = iso_stm env s
	    val (ds2, ss2) = iso_stms env ss
	in (ds1 @ ds2, ss1 @ ss2) end

    and iso_decls env (A.VarDecl(id, tp, NONE, ext)::ds) =
	let val (ds', ss', env') = iso_decls (Symbol.bind env (id, tp)) ds
	in ([A.VarDecl(id, tp, NONE, ext)] @ ds', ss', env') end
      | iso_decls env (A.VarDecl(id, tp, SOME(e), ext)::ds) =
	let val (ds1, ss1, p1) = iso_exp env e
	    val (ds2, ss2, env') = iso_decls (Symbol.bind env (id, tp)) ds
	in (ds1 @ [A.VarDecl(id, tp, NONE, ext)] @ ds2,
	    ss1 @ [A.Assign(NONE, A.Var(id), p1)] @ ss2,
	    env')
	end
      | iso_decls env nil = (nil, nil, env)

    and iso_funcall env (A.FunCall(g, es)) =
	let val (ds, ss, ps) = iso_exps env es
	in
	    (ds, ss @ [A.Exp(A.FunCall(g, ps))])
	end 
      | iso_funcall env (A.Marked(marked_exp)) =
	  iso_funcall env (Mark.data marked_exp)

    and iso_assign env (oper_opt as (SOME _)) (ds1, ss1, lv1) e =
	let
	    val (ds2, ss2, p2) = iso_exp env e
	in
	    (ds1 @ ds2, ss1 @ ss2 @ [A.Assign(oper_opt, lv1, p2)])
	end
      | iso_assign env (NONE) (ds1, ss1, lv1 as A.Var _) e =
	let
	    val (ds2, ss2, p2) = iso_exp env e
	in
	    (ds1 @ ds2, ss1 @ ss2 @ [A.Assign(NONE, lv1, p2)])
	end
      | iso_assign env (NONE) (ds1, ss1, lv1 as A.OpExp(A.DEREF, _)) e =
        let
	    val (ds2, ss2, p2) = iso_exp env e
	in
	    (ds1 @ ds2, ss1 @ ss2 @ [A.Assign(NONE, lv1, p2)])
	end
      | iso_assign env (NONE) (ds1, ss1, lv1) e = (* lv1 = A[p] | lv2->f *)
	let
	    (*
	    val (d, t) = Syn.new_tmp(A.Pointer(Syn.syn_exp env e))
	     *)
            (* previous line does not work if e = NULL *)
	    val env1 = extend_env env ds1
	    val (d, t) = Syn.new_tmp(A.Pointer(Syn.syn_exp env1 lv1))
	    val (ds2, ss2, p2) = iso_exp env e
	in
	    (ds1 @ [d] @ ds2,
	     ss1 @ [A.Assign(SOME(A.DEREF), t, lv1)] (* hack: t <*>= e means t = &e *)
	     @ ss2 @ [A.Assign(NONE, A.OpExp(A.DEREF, [t]), p2)])
	end

    (*
     * Printing, under the assumption that effects have been isolated
     *)

    fun is_external g =
	( case Symtab.lookup g
	   of SOME(A.Function(g', rtp, params, bodyOpt, specs, is_extern, ext)) => is_extern
	    | _ => false )

    fun pp_field f = "_c0_" ^ Symbol.name f
    fun pp_struct s = "struct _c0_" ^ Symbol.name s
    fun pp_typename t = "_c0_" ^ Symbol.name t
    fun pp_var id = "_c0v_" ^ Symbol.name id
    fun pp_fun id =
	let
	    val name = Symbol.name id
	in
	    if is_external id
	    then name
	    else "_c0_" ^ name
	end
    fun pp_extfun id = Symbol.name id (* extern function: do not munge *)

    fun pp_tp (A.Int) = "unsigned" (* Dec 2010, to guarantee modular arithmetic *)
      | pp_tp (A.Bool) = "bool" (* == int *)
      | pp_tp (A.String) = "c0_string" (* "abstract" *)
      | pp_tp (A.Char) = "char" (* "abstract" *)
      | pp_tp (A.Pointer(tp)) = pp_tp tp ^ "*"
      | pp_tp (A.Array(tp)) = "cc0_array(" ^ pp_tp tp ^ ")"
      | pp_tp (A.StructName(s)) = pp_struct s
      | pp_tp (A.TypeName(t)) = pp_typename t
      | pp_tp (A.Void) = "void"
      | pp_tp (A.Any) = "void"

    fun pp_oper A.LOGNOT = "!"
      | pp_oper A.COMPLEMENT = "~"
      | pp_oper A.NEGATIVE = "-"
      | pp_oper A.DEREF = "*"
      | pp_oper A.TIMES = "*"
      (*
      | pp_oper A.DIVIDEDBY = "/"
      | pp_oper A.MODULO = "%"
      *)
      | pp_oper A.PLUS = "+"
      | pp_oper A.MINUS = "-"
      (*
      | pp_oper A.SHIFTLEFT = "<<"
      | pp_oper A.SHIFTRIGHT = ">>"
      *)
      | pp_oper A.LESS = "<"
      | pp_oper A.LEQ = "<="
      | pp_oper A.GREATER = ">"
      | pp_oper A.GEQ = ">="
      | pp_oper A.EQ = "=="
      | pp_oper A.NOTEQ = "!="
      | pp_oper A.AND = "&"
      | pp_oper A.XOR = "^"
      | pp_oper A.OR = "|"
      | pp_oper A.LOGAND = "&&"
      | pp_oper A.LOGOR = "||"

    fun pp_exp env (A.Var(id)) = pp_var id
      | pp_exp env (A.IntConst(w)) = (* bug workaround for gcc -fwrapv, Jan 22, 2012 *)
	if (w = Word32Signed.TMIN) then "(1<<31)" else Word32Signed.toString w
      | pp_exp env (A.StringConst(s)) = "c0_string_fromliteral(\"" ^ String.toCString s ^ "\")"
      | pp_exp env (A.CharConst(c)) = "'" ^ Char.toCString c ^ "'"
      | pp_exp env (A.True) = "true"
      | pp_exp env (A.False) = "false"
      | pp_exp env (A.Null) = "NULL"
      | pp_exp env (A.OpExp(A.DIVIDEDBY, [e1, e2])) =
	"_idiv(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(A.MODULO, [e1, e2])) =
	"_imod(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(A.SHIFTLEFT, [e1, e2])) =
	"_sal(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(A.SHIFTRIGHT, [e1, e2])) =
	"_sar(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      (* comparisons always need to be done on signed integers *)
      | pp_exp env (e as A.OpExp(A.LESS, _)) = pp_comparison env e
      | pp_exp env (e as A.OpExp(A.LEQ, _)) = pp_comparison env e
      | pp_exp env (e as A.OpExp(A.GREATER, _)) = pp_comparison env e
      | pp_exp env (e as A.OpExp(A.GEQ, _)) = pp_comparison env e
      | pp_exp env (A.OpExp(A.SUB, [e1,e2])) =
	let val A.Array(tp) = Syn.syn_exp_expd env e1
	in
	    "cc0_array_sub(" ^ pp_tp tp ^ "," ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
	end
      | pp_exp env (A.OpExp(A.DEREF, [e1])) =
	let val A.Pointer(tp) = Syn.syn_exp_expd env e1
	in "cc0_deref(" ^ pp_tp tp ^ ", " ^ pp_exp env e1 ^ ")" end
      | pp_exp env (A.OpExp(A.COND, [e1, e2, e3])) =
        "(" ^ pp_exp env e1 ^ " ? " ^ pp_exp env e2 ^ " : " ^ pp_exp env e3 ^ ")"
      | pp_exp env (A.OpExp(oper, [e])) =
	pp_oper oper ^ "(" ^ pp_exp env e ^ ")"
      | pp_exp env (A.OpExp(oper, [e1,e2])) =
	"(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.Select(e, f)) =
	"(" ^ pp_exp env e ^ ")." ^ pp_field f
      | pp_exp env (A.FunCall(id, es)) =
	  pp_fun id ^ "(" ^ pp_exps env es ^ ")"
      | pp_exp env (A.Alloc(tp)) = "cc0_alloc(" ^ pp_tp tp ^ ")"
      | pp_exp env (A.AllocArray(tp, e)) = "cc0_alloc_array(" ^ pp_tp tp ^ "," ^ pp_exp env e ^ ")"
      | pp_exp env (A.Result) = (* should be impossible, except in comment *)
	  "\\result"
      | pp_exp env (A.Length(e)) = "c0_array_length(" ^ pp_exp env e ^ ")"
      | pp_exp env (A.Old(e)) = (* should be impossible, except in comment *)
	  "\\old(" ^ pp_exp env e ^ ")"
      | pp_exp env (A.Marked(marked_exp)) =
	  pp_exp env (Mark.data marked_exp)

    and pp_exps env nil = ""
      | pp_exps env (e::nil) = pp_exp env e
      | pp_exps env (e::es) = pp_exp env e ^ ", " ^ pp_exps env es

    and pp_stringlist env nil = "\"\""
      | pp_stringlist env (e::nil) = pp_exp env e
      | pp_stringlist env (e::es) =
	"c0_string_join(" ^ pp_exp env e ^ ", " ^ pp_stringlist env es ^ ")"

   and pp_comparison env (A.OpExp(oper, [e1, e2])) =
	"(((int)" ^ pp_exp env e1 ^ ")" ^ pp_oper oper ^ "((int)"
	^ pp_exp env e2 ^ "))"

    fun pp_assign_effect_op env (cname, A.Var(id), e) =
	  pp_var id ^ " = " ^ cname ^ "(" ^ pp_var id ^ "," ^ pp_exp env e ^ ");"
      | pp_assign_effect_op env (cname, A.Marked(marked_exp), e) =
	  pp_assign_effect_op env (cname, Mark.data marked_exp, e)
      | pp_assign_effect_op env (cname, lv, e) = (* lv != x *)
	  cname ^ "_asn(&" ^ pp_exp env lv ^ "," ^ pp_exp env e ^ ");"

    fun pp_assign env (A.Assign(NONE, lv, e)) =
	  pp_exp env lv ^ " = " ^ pp_exp env e ^ ";"
      | pp_assign env (A.Assign(SOME(A.DEREF), lv, e)) =
          (* hack: x <*>= e means x = &e *)
	  pp_exp env lv ^ " = " ^ "&(" ^ pp_exp env e ^ ")" ^ ";"
      | pp_assign env (A.Assign(SOME(A.DIVIDEDBY), lv, e)) =
	  pp_assign_effect_op env ("_idiv", lv, e)
      | pp_assign env (A.Assign(SOME(A.MODULO), lv, e)) =
	  pp_assign_effect_op env ("_imod", lv, e)
      | pp_assign env (A.Assign(SOME(A.SHIFTLEFT), lv, e)) =
	  pp_assign_effect_op env ("_sal", lv, e)
      | pp_assign env (A.Assign(SOME(A.SHIFTRIGHT), lv, e)) =
	  pp_assign_effect_op env ("_sar", lv, e)
      | pp_assign env (A.Assign(SOME(oper), lv, e)) =
	  pp_exp env lv ^ " " ^ pp_oper oper ^ "= " ^ pp_exp env e ^ ";"

    fun pp_stm env (s as A.Assign (oper_opt, lv, e)) =
          pp_assign env s
      | pp_stm env (A.Exp(e)) =
	  (* effects have been isolated *)
	  pp_exp env e ^ ";\n"
      | pp_stm env (A.Seq(nil, nil)) = "{ }"
      | pp_stm env (A.Seq(ds, ss)) =
	let val env' = Syn.syn_decls env ds
	in 
	    "{\n" ^ pp_decls env ds ^ pp_stms env' ss ^ "\n}"
	end
      | pp_stm env (A.If(e, s1, s2)) =
	  "if (" ^ pp_exp env e ^ ")\n"
	  ^ pp_stm env s1 ^ "\n"
	  ^ "else\n"
	  ^ pp_stm env s2
      (* no while statement allowed; isolated into for loops *)
      (*
      | pp_stm env (A.While(e, s)) =
	  "while (" ^ pp_exp env e ^ ")\n"
	  ^ pp_stm env s
      *)
      | pp_stm env (A.For(A.Seq([],[]), e2, A.Seq([],[]), _, s4)) =
	  "while (" ^ pp_exp env e2 ^ ")\n"
	  ^ pp_stm env s4
      | pp_stm env (A.For(s1, e2, s3, _, s4)) =
	(* by isolation invariant, s1 = s3 ! *)
        (* This is not ISO-C, which would require duplicating s1 *)
	  "while (({" ^ pp_stm env s1 ^ pp_exp env e2 ^ ";}))\n"
	  ^ pp_stm env s4
      | pp_stm env (A.Continue) = "continue;"
      | pp_stm env (A.Break) = "break;"
      | pp_stm env (A.Return(SOME(e))) =
	  "return " ^ pp_exp env e ^ ";"
      | pp_stm env (A.Return(NONE)) =
	  "return;"
      | pp_stm env (A.Assert(e1, e2s)) =
	  "cc0_assert(" ^ pp_exp env e1 ^ ", " ^ pp_stringlist env e2s ^ ");\n"
      | pp_stm env (A.Anno(specs)) = (* should not arise *)
	  ";"
      | pp_stm env (A.Markeds(marked_stm)) =
	  pp_stm env (Mark.data marked_stm)

    and pp_stms env nil = ""
      | pp_stms env (s::nil) = pp_stm env s
      | pp_stms env (s::ss) = pp_stm env s ^ "\n" ^ pp_stms env ss

    and pp_decl env (A.VarDecl(id, tp, NONE, ext)) =
	  pp_tp tp ^ " " ^ pp_var id ^ ";\n"
      | pp_decl env (A.VarDecl(id, tp, SOME(e), ext)) =
	  pp_tp tp ^ " " ^ pp_var id ^ " = " ^ pp_exp env e ^ ";\n"

    and pp_decls env nil = ""
      | pp_decls env (d::ds) =
	  pp_decl env d ^ pp_decls (Syn.syn_decls env [d]) ds

    fun pp_param (id, tp) =
	  pp_tp tp ^ " " ^ pp_var id

    fun pp_params nil = ""
      | pp_params (A.VarDecl(id,tp,NONE,ext)::nil) = pp_param (id, tp)
      | pp_params (A.VarDecl(id,tp,NONE,ext)::params) =
	  pp_param (id, tp) ^ ", " ^ pp_params params

    fun pp_fields nil = ""
      | pp_fields (A.Field(f,tp,ext)::fields) =
	  pp_tp tp ^ " " ^ pp_field f ^ ";\n"
	  ^ pp_fields fields

    fun pp_gdecl (A.Struct(s, NONE, is_external, ext)) =
	  pp_struct s ^ ";\n"
      | pp_gdecl (A.Struct(s, SOME(fields), is_external, ext)) =
	  pp_struct s ^ " {\n" ^ pp_fields fields ^ "};\n"
      | pp_gdecl (A.Function(g, result, params, NONE, specs, is_extern, ext)) =
	  (if is_extern then "extern " else "")
	  ^ pp_tp result ^ " " ^ pp_fun g ^ "(" ^ pp_params params ^ ");\n"
      | pp_gdecl (A.Function(g, rtp, params, SOME(s), _, _, ext)) =
	let
	    val env0 = Syn.syn_decls Symbol.empty params
	    val env1 = Symbol.bind env0 (Symbol.symbol "\\result", rtp)
	    val (ds, ss) = iso_stm env1 (s)
	in
	    pp_tp rtp ^ " " ^ pp_fun g ^ "("
	    ^ pp_params params ^ ") {\n"
	    ^ pp_decls env1 ds
	    ^ pp_stms (Syn.syn_decls env1 ds) ss ^ "\n}\n"
	end
      | pp_gdecl (A.TypeDef(t, tp, ext)) =
	"typedef " ^ pp_tp tp ^ " " ^ pp_typename t ^ ";\n"
      | pp_gdecl (A.Pragma(A.UseLib(libname, SOME(gdecls)), ext)) =
	"//#use <" ^ libname ^ ">\n"
	^ pp_gdecls gdecls
      | pp_gdecl (A.Pragma(A.UseFile(filename, SOME(gdecls)), ext)) =
	"//#use \"" ^ filename ^ "\"\n"
	^ pp_gdecls gdecls
      | pp_gdecl (A.Pragma(A.Raw(pname, pargs), ext)) =
	"//" ^ pname ^ pargs ^ "\n"

    and pp_gdecls nil = ""
      | pp_gdecls (gdecl::gdecls) =
          pp_gdecl gdecl ^ pp_gdecls gdecls

    fun pp_program gdecls include_files opt_level =
        (* strcts must be sorted in dependency order; see TypeChecker.sort *)
          String.concat 
            (map (fn include_file => "#include \"" ^ include_file ^ "\"\n\n")
                 include_files)
          ^ pp_gdecls gdecls

end
