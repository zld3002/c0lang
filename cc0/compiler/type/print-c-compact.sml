(* C0 Compiler
 * Printing to C
 * Author: Frank Pfenning <fp@cs.cmu.edu>
 *
 *)

signature PRINT =
sig
    val pp_program : Ast.program -> string
end

(* There are a number of semantic differences that require some care
 * when printing to C.  Some of these are smoothed out by appropriate
 * macros in the various runtimes (c0rt [default], bare [without gc],
 * unsafe [without null-ptr or array bounds checks]).  Others are
 * dealt with here.  We also make certain assumptions about the
 * compilation model used by the specific gcc backend we use.
 *
 * Assumptions:
 * - int has 32 bits.  This file should probably print 'int' as 'int32'.
 * - int used two's complement arithmetic for +, -, *.  This is
 *   achieved by passing -fwrapv to gcc.  An alternative using
 *   unsigned int's in C is awkward (see some comments below).
 * - we assume right shift e1 >> e2 is arithmetical on negative e1.
 *
 * Working around undefined behavior:
 * - null ptr deref is handled by macro cc0_deref(tp, e)
 * - array bounds checking is handled by macro cc0_array_sub(tp, e1, e2)
 *   both of these also work as lvalues for assignments
 * - allocation is handled by macro cc0_alloc(tp)
 * - array allocation is handled by macro cc0_alloc_array(tp, e)
 *   allocations raise an exception if they fail, rather than returning NULL
 *   they also initialize to 0
 * - assertions are handled with macro cc0_assert(e, msg1, msg2, ...)
 * - e1/e2 is compiled as c0_idiv(e1,e2) to check for overflow
 * - e1%e2 is compiled as c0_imod(e1,e2) to check for overflow
 * - e1<<e2 is compiled as c0_sal(e1,e2) to check range on e2
 * - e1>>e2 is compiled as c0_sar(e1,e2) to check range on e2
 * - evaluation order is undefined, which is handled by isolating
 *   expressions which may have an effect.  For example,
 *   f(g(x),h(3)) might be translated as
 *   int tmp1 = g(x);
 *   int tmp2 = h(3);
 *   int tmp3 = f(tmp1,tmp2);
 *   and then using "tmp3" where the above expression was embedded.
 *   This is explained further in the iso_<cat> functions below.
 *)

structure PrintC =
struct

   structure A = Ast

   (* extend_env env ds = env', extending env with declarations in ds
    * we assume there is no shadowing or name clashes *)
   fun extend_env env (A.VarDecl(id, tp, _, ext)::ds) =
         extend_env (Symbol.bind env (id, tp)) ds
     | extend_env env nil = env

   val MINUSONE = Word32.fromInt(~1);
   val THIRTYTWO = Word32.fromInt(32);

   (* is_safe_div p = true if n / p and n % p are known to be defined, for all n.
    * We assume p is a pure expression, without marks. *)
   fun is_safe_div (A.IntConst(w)) =
       w <> Word32Signed.ZERO andalso w <> MINUSONE
     | is_safe_div _ = false

   (* is_safe_shift k = true if 0 <= k & k < 32, so n << k and n >> k is defined.
    * assumes n >> k for negative n is arithmetic right shift, not logical *)
   fun is_safe_shift (A.IntConst(w)) = Word32.<(w, THIRTYTWO)
     | is_safe_shift _ = false

    (*
     * Printing, under the assumption that effects have been isolated
     *)
    fun is_external g =
	( case Symtab.lookup g
	   of SOME(A.Function(g', rtp, params, bodyOpt, specs, is_extern, ext)) => is_extern
	    | _ => false )

    (* add_stmdecl env s = env', adding declaration d to env in case
     * s is a declaration-as-statement d *)
    fun add_stmdecl env (A.StmDecl(A.VarDecl(id, tp, _, _))) = Symbol.bind env (id, tp)
      | add_stmdecl env _ = env

    (* indent n str = str', only to be used for string
     * at beginning of line.  Used to make output more readable. *)
    fun indent n str = (StringCvt.padLeft #" " n "") ^ str

    (* is_nop s = true, if s is a nop, or sequence of nops.
     * Used to make output more readable. *)
    fun is_nop (A.Seq([], ss)) = is_nops ss
      | is_nop _ = false
    and is_nops nil = true
      | is_nops (s::ss) = is_nop s andalso is_nops ss

    (* Name mangling, to avoid conflict with C keywords and
     * with each other.  Readability of code could be improved
     * by only doing this when necessary *)
    fun pp_field f = "_c0_" ^ Symbol.name f
    fun pp_struct s = "struct _c0_" ^ Symbol.name s
    fun pp_typename t = "_c0_" ^ Symbol.name t
    fun pp_var id =
        case Symbol.nname id
          of (Symbol.User, name) => "_c0v_" ^ name
             (* '_c0v_' avoids shadowing of functions with local variables *)
           | (Symbol.Internal, name) => "_c0t_" ^ name
             (* '_c0t_' avoids conflict between user and internal names *)
             (* code itself is responsible for freshness *)
    fun pp_fun id =
        case Symbol.nname id
         of (Symbol.User, name) =>
            if is_external id   (* difficult to fold into namespace; use symbol table *)
            then name
            else "_c0_" ^ name
          | (Symbol.Internal, name) => "_c0t_" ^ name

    (* pp_tp tp = str, converting tp to C equivalent *)
    fun pp_tp (A.Int) = "int"	       (* should be: int32_t in <stdint.h>? *)
      | pp_tp (A.Bool) = "bool"	       (* in <stdbool.h> *)
      | pp_tp (A.String) = "c0_string" (* "abstract", typically char* *)
      | pp_tp (A.Char) = "char"	       (* "abstract", typically char *)
      | pp_tp (A.Pointer(tp)) = pp_tp tp ^ "*"
      | pp_tp (A.Array(tp)) = "cc0_array(" ^ pp_tp tp ^ ")" (* typically, struct of length and tp* *)
      | pp_tp (A.StructName(s)) = pp_struct s
      | pp_tp (A.TypeName(t)) = pp_typename t
      | pp_tp (A.Void) = "void"        (* for function return *)
      | pp_tp (A.Any) = "void"	       (* for NULL, which has type A.Pointer(A.Any) *)

    (* pp_oper oper = str, converting operator to C equivalent *)
    fun pp_oper A.LOGNOT = "!"
      | pp_oper A.COMPLEMENT = "~"
      | pp_oper A.NEGATIVE = "-"
      | pp_oper A.DEREF = "*"
      | pp_oper A.TIMES = "*"
      | pp_oper A.DIVIDEDBY = "/"   (* for save div *)
      | pp_oper A.MODULO = "%"	    (* for safe mod *)
      | pp_oper A.PLUS = "+"
      | pp_oper A.MINUS = "-"
      | pp_oper A.SHIFTLEFT = "<<"  (* for safe sal *)
      | pp_oper A.SHIFTRIGHT = ">>" (* for safe sar *)
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

    (* pp_exp env e = str, converting expression to C equivalent.
     * Uses only one line and parentheses liberally to disambiguate.
     * Also uses various macros to allow safe and unsafe runtimes.
     * See c0/include/cc0lib.h and c0/include/c0rt.h *)
    fun pp_exp env (A.Var(id)) = pp_var id
      | pp_exp env (A.IntConst(w)) = (* bug workaround for gcc -fwrapv, Jan 22, 2012 *)
	if (w = Word32Signed.TMIN) then "(-2147483647-1)" else Word32Signed.toString w
      | pp_exp env (A.StringConst(s)) = "c0_string_fromliteral(\"" ^ String.toCString s ^ "\")"
      | pp_exp env (A.CharConst(c)) = "'" ^ Char.toCString c ^ "'"
      | pp_exp env (A.True) = "true"
      | pp_exp env (A.False) = "false"
      | pp_exp env (A.Null) = "NULL"
      | pp_exp env (A.OpExp(oper as A.DIVIDEDBY, [e1, e2])) =
	if is_safe_div e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "c0_idiv(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(oper as A.MODULO, [e1, e2])) =
	if is_safe_div e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "c0_imod(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(oper as A.SHIFTLEFT, [e1, e2])) =
	if is_safe_shift e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "c0_sal(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
      | pp_exp env (A.OpExp(oper as A.SHIFTRIGHT, [e1, e2])) =
	if is_safe_shift e2
	then "(" ^ pp_exp env e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp env e2 ^ ")"
	else "c0_sar(" ^ pp_exp env e1 ^ "," ^ pp_exp env e2 ^ ")"
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

    fun pp_assign env (A.Assign(NONE, lv, e)) =
	  pp_exp env lv ^ " = " ^ pp_exp env e ^ ";"
      | pp_assign env (A.Assign(SOME(A.DEREF), lv, e)) =
          (* hack: x <*>= e means x = &e *)
	  pp_exp env lv ^ " = " ^ "&(" ^ pp_exp env e ^ ")" ^ ";"
      (* next four are effectful: call runtime function *)
      | pp_assign env (A.Assign(SOME(A.DIVIDEDBY), lv, e)) =
          pp_exp env lv ^ " = " ^ "c0_idiv(" ^ pp_exp env lv ^ "," ^ pp_exp env e ^ ");"
      | pp_assign env (A.Assign(SOME(A.MODULO), lv, e)) =
          pp_exp env lv ^ " = " ^ "c0_imod(" ^ pp_exp env lv ^ "," ^ pp_exp env e ^ ");"
      | pp_assign env (A.Assign(SOME(A.SHIFTLEFT), lv, e)) =
          pp_exp env lv ^ " = " ^ "c0_sal(" ^ pp_exp env lv ^ "," ^ pp_exp env e ^ ");"
      | pp_assign env (A.Assign(SOME(A.SHIFTRIGHT), lv, e)) =
          pp_exp env lv ^ " = " ^ "c0_sar(" ^ pp_exp env lv ^ "," ^ pp_exp env e ^ ");"
      (* remaining ones are pure: map to corresponding C construct *)
      | pp_assign env (A.Assign(SOME(oper), lv, e)) =
	  pp_exp env lv ^ " " ^ pp_oper oper ^ "= " ^ pp_exp env e ^ ";"

    (* pp_stm n env s = str
     * pp_stms n env ss = str
     * pp_decl n env d = str
     * pp_decls n env ds = str
     * Convert statement(s) or declaration(s) to string, in
     * environment env, indenting new lines n spaces.
     * Assume body of while-loop and branches of conditional
     * are sequences, which is guaranteed by iso_<cat>.
     * Also, statements are free of for-loops *)
    fun pp_stm n env (s as A.Assign (oper_opt, lv, e)) =
          indent n (pp_assign env s)
      | pp_stm n env (A.Exp(e)) =
	  (* effects have been isolated *)
	  indent n (pp_exp env e ^ ";")
      | pp_stm n env (A.Seq(nil, nil)) =
	  indent n "{ }"
      | pp_stm n env (A.Seq(nil, [s' as A.Seq _])) =
	  (* compress nested sequences *)
	  pp_stm n env s'
      | pp_stm n env (A.Seq(ds, ss)) =
	let val env' = Syn.syn_decls env ds
	in
	    indent n "{\n"
	    ^ pp_decls (n+2) env ds
	    ^ pp_stms (n+2) env' ss
	    ^ indent n "}"
	end
      | pp_stm n env (A.StmDecl(d)) =
	let val env' = Syn.syn_decls env [d]
	in
	    pp_decl n env d
	end
      | pp_stm n env (A.If(e, A.Seq([], ss1), A.Seq([], ss2))) =
	indent n ("if (" ^ pp_exp env e ^ ") {\n")
	^ pp_stms (n+2) env ss1
	^ indent n "}"
        ^ (if is_nops ss2
	   then "" (* ok, since braces delimit scope? *)
	   else " else {\n" ^ pp_stms (n+2) env ss2
		^ indent n "}")
      | pp_stm n env (A.While(e, _, A.Seq([], ss))) =
	indent n ("while (" ^ pp_exp env e ^ ") {\n")
	^ pp_stms (n+2) env ss
	^ indent n "}"
      (* no A.For *)
      | pp_stm n env (A.Continue) = indent n "continue;"
      | pp_stm n env (A.Break) = indent n "break;"
      | pp_stm n env (A.Return(SOME(e))) =
	  indent n ("return " ^ pp_exp env e ^ ";")
      | pp_stm n env (A.Return(NONE)) =
	  indent n "return;"
      | pp_stm n env (A.Assert(e1, e2s)) =
          (* We reduce e2s to a single string by concatenation, to avoid
           * variadic functions or macros *)
	  indent n ("cc0_assert(" ^ pp_exp env e1 ^ ", " ^ pp_stringlist env e2s ^ ");")
      | pp_stm n env (A.Error(e)) =
          indent n ("c0_error(" ^ pp_exp env e ^ ");\n") 
          ^ indent n ("exit(EXIT_FAILURE);")
      | pp_stm n env (A.Anno(specs)) = (* should not arise *)
	  indent n ";"
      | pp_stm n env (A.Markeds(marked_stm)) =
	  pp_stm n env (Mark.data marked_stm)

    and pp_stms n env nil = ""
      | pp_stms n env (A.Seq([],ss1)::nil) =
	  (* avoid spurious blocks, tail must be nil to avoid incorrect
           * mixing of scopes *)
	  pp_stms n env ss1
      | pp_stms n env (s::ss) =
          (* update environment if s is declaration d *)
	  pp_stm n env s ^ "\n"
	  ^ pp_stms n (add_stmdecl env s) ss

    and pp_decl n env (A.VarDecl(id, tp, NONE, ext)) =
	  indent n (pp_tp tp ^ " " ^ pp_var id ^ ";")
      | pp_decl n env (A.VarDecl(id, tp, SOME(e), ext)) =
	  indent n (pp_tp tp ^ " " ^ pp_var id ^ " = " ^ pp_exp env e ^ ";")

    and pp_decls n env nil = ""
      | pp_decls n env (d::ds) =
	  pp_decl n env d ^ "\n"
	  ^ pp_decls n (Syn.syn_decls env [d]) ds

    fun pp_param (id, tp) =
	  pp_tp tp ^ " " ^ pp_var id

    (* pp_params ds = str, converting parameter list to string *)
    fun pp_params nil = ""
      | pp_params (A.VarDecl(id,tp,NONE,ext)::nil) = pp_param (id, tp)
      | pp_params (A.VarDecl(id,tp,NONE,ext)::params) =
	  pp_param (id, tp) ^ ", " ^ pp_params params

    (* pp_fields n fields = str, converting list of fields to string *)
    fun pp_fields n nil = ""
      | pp_fields n (A.Field(f,tp,ext)::fields) =
	  indent n (pp_tp tp ^ " " ^ pp_field f ^ ";\n")
	  ^ pp_fields n fields

    (* pp_gdecl gdecl = str
     * pp_gdecls gdecls = str
     * converting global declaration to string *)
    fun pp_gdecl (A.Struct(s, NONE, is_external, ext)) =
	  pp_struct s ^ ";\n"
      | pp_gdecl (A.Struct(s, SOME(fields), is_external, ext)) =
	  pp_struct s ^ " {\n" ^ pp_fields 2 fields ^ "};\n"
      | pp_gdecl (A.Function(g, result, params, NONE, specs, is_extern, ext)) =
	  (if is_extern then "extern " else "")
	  ^ pp_tp result ^ " " ^ pp_fun g ^ "(" ^ pp_params params ^ ");\n"
      | pp_gdecl (A.Function(g, rtp, params, SOME(s), _, _, ext)) =
	let
	    val env = Syn.syn_decls Symbol.empty params
	    val ss = Isolate.iso_stm env s
	in (* newline before function definitions *)
	    "\n" ^ pp_tp rtp ^ " " ^ pp_fun g ^ "("
	    ^ pp_params params ^ ") {\n"
	    ^ pp_stms 2 env ss
	    ^ "}\n"
	end
      | pp_gdecl (A.TypeDef(aid, tp, ext)) =
	"typedef " ^ pp_tp tp ^ " " ^ pp_typename aid ^ ";\n"

      (* pragmas are included as comments in C file *)
      | pp_gdecl (A.Pragma(A.UseLib(libname, SOME(gdecls)), ext)) =
	"\n//#use <" ^ libname ^ ">\n"
	^ pp_gdecls gdecls
	^ "// end <" ^ libname ^ ">\n"
      | pp_gdecl (A.Pragma(A.UseFile(filename, SOME(gdecls)), ext)) =
	"\n//#use \"" ^ filename ^ "\"\n"
	^ pp_gdecls gdecls
	^ "// end \"" ^ filename ^ "\"\n"
      | pp_gdecl (A.Pragma(A.Raw(pname, pargs), ext)) =
	"\n//" ^ pname ^ pargs ^ "\n"

    and pp_gdecls nil = ""
      | pp_gdecls (gdecl::gdecls) =
          pp_gdecl gdecl ^ pp_gdecls gdecls

    (* pp_program gdecls include_files = str
     * Convert program consisting of gdecls to a string, including
     * include_files. *)
    fun pp_program gdecls include_files =
          String.concat 
            (map (fn include_file => "#include \"" ^ include_file ^ "\"\n")
                 include_files)
          ^ pp_gdecls gdecls

end
