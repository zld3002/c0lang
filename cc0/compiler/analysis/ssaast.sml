(* VAST is AST with one change made: Variables can carry a version number *)
signature VAST =
sig
  type ident = Ast.ident
  type tp = Ast.tp
  type oper = Ast.oper

  type ext = Mark.ext option

  (* Expressions *)
  datatype exp =
      (* SVar is the most important change made. It allows for version numbers. *)
      SVar of ident * int 		  (* x_i *)
    | IntConst of Word32.word	  (* n, -2^31 <= n < 2^31 *)
    | StringConst of string       (* "..." *)
    | CharConst of char		  (* 'c' *)
    | True			  (* true *)
    | False			  (* false *)
    | Null			  (* NULL *)
    | OpExp of oper * exp list	  (* oper(e1,...,en) *)
    | Select of exp * ident       (* e.f or e->f *)
    | FunCall of ident * exp list (* g(e1,...,en) *)
    | AddrOf of ident             (* &g *)
    | Invoke of exp * exp list    (* (e)(e1,...,en) *)
    | Alloc of tp		  (* alloc(tp) *)
    | AllocArray of tp * exp	  (* alloc_array(tp,e) *)
    | Cast of tp * exp            (* (tp)e *)
    | Result			  (* \result, in @ensures *)
    | Length of exp		  (* \length(e), in contracts *)
    | Hastag of tp * exp          (* \hastype(tp,e), in contracts *)
    | Marked of exp Mark.marked	  (* mark with source region info *)

  (* Statements *)
  datatype stm =
      Assign of oper option * exp * exp     (* lv = e; or lv op= e; *)
    | Exp of exp			    (* e; *)
    | Seq of stm list	    (* { stms } *)
    | StmDecl of svardecl		    (* d *)
    | If of exp * stm * stm		    (* if (e) s1 else s2 *)
    | While of exp * spec list * stm            (* while (e) s, loop invs. *)
    | For of stm * exp * stm * spec list * stm  (* for (s1; e; s2) s3, loop invs. *)
    | Continue				    (* continue; *)
    | Break				    (* break; *)
    | Return of exp option		    (* return [e]; *)
    | Assert of exp * exp list              (* assert(e); error msgs *)
    | Error of exp                          (* error(e); *)
    | Anno of spec list		            (* @assert or @loop_invariant *)
    | Markeds of stm Mark.marked            (* mark with source region info *)

  (* Variable declarations
  and vardecl =			    (* tp x; or tp x = e; *)
      VarDecl of ident * int * tp * exp option * ext *)
  (* reserve Ast.VarDecl for types *)
  (* define something new called SVarDecl for Function decl. *)
  (* need to define a new global Function decl. as well *)
  (* leave Ast.tp unchanged*)
  datatype svardecl =
      SVarDecl of ident * int * tp * exp option * ext



  (* Global declarations *)
  datatype gdecl =
      Struct of ident * field list option * bool * ext
                                (* struct s; or struct s {...}; *)
    | TypeDef of ident * tp * ext (* typedef tp aid *)
    | FunTypeDef of ident * tp * vardecl list * spec list * ext
                                (* typedef rtp ftpname(tp1 x1, ..., tpn xn); *)
                                (* specs = pre/postconditions *)
    | Function of ident * tp * vardecl list * stm option
                  * spec list * bool * ext
                                (* rtp g(tp1 x1, ..., tpn xn); or *)
                                (* rtp g(tp1 x1, ..., tpn xn) { body } *)
                                (* specs = pre/postconditions, bool = is_external *)
    | Pragma of pragma * ext	(* #<pragma> ... *)

  (* Fields of structs *)
  datatype field =
      Field of ident * tp * ext	(* tp f; *)

  (* Specs (for contracts) *)
  datatype spec =
      Requires of exp * ext	 (* @requires *)
    | Ensures of exp * ext	 (* @ensures *)
    | LoopInvariant of exp * ext (* @loop_invariant *)
    | Assertion of exp * ext	 (* @assert *)


  (* Programs *)
  type program = gdecl list

  

  (* print abstract syntax, with redundant parentheses *)
  structure Print :
  sig
    val pp_tp : tp -> string
    val pp_oper : oper -> string
    val pp_exp : exp -> string
    val pp_stm : stm -> string
    val pp_program : program -> string
  end

end

structure VAst :> VAST =
struct
  type ident = Ast.ident
  type tp = Ast.tp
  type oper = Ast.oper

  type ext = Mark.ext option

  (* Expressions *)
  datatype exp =
      (* SVar is the most important change made. It allows for version numbers. *)
      SVar of ident * int 		  (* x_i *)
    | IntConst of Word32.word	  (* n, -2^31 <= n < 2^31 *)
    | StringConst of string       (* "..." *)
    | CharConst of char		  (* 'c' *)
    | True			  (* true *)
    | False			  (* false *)
    | Null			  (* NULL *)
    | OpExp of oper * exp list	  (* oper(e1,...,en) *)
    | Select of exp * ident       (* e.f or e->f *)
    | FunCall of ident * exp list (* g(e1,...,en) *)
    | AddrOf of ident             (* &g *)
    | Invoke of exp * exp list    (* (e)(e1,...,en) *)
    | Alloc of tp		  (* alloc(tp) *)
    | AllocArray of tp * exp	  (* alloc_array(tp,e) *)
    | Cast of tp * exp            (* (tp)e *)
    | Result			  (* \result, in @ensures *)
    | Length of exp		  (* \length(e), in contracts *)
    | Hastag of tp * exp          (* \hastype(tp,e), in contracts *)
    | Marked of exp Mark.marked	  (* mark with source region info *)

  (* Statements *)
  datatype stm =
      Assign of oper option * exp * exp     (* lv = e; or lv op= e; *)
    | Exp of exp			    (* e; *)
    | Seq of vardecl list * stm list	    (* { ds es } *)
    | StmDecl of vardecl		    (* d *)
    | If of exp * stm * stm		    (* if (e) s1 else s2 *)
    | While of exp * spec list * stm            (* while (e) s, loop invs. *)
    | For of stm * exp * stm * spec list * stm  (* for (s1; e; s2) s3, loop invs. *)
    | Continue				    (* continue; *)
    | Break				    (* break; *)
    | Return of exp option		    (* return [e]; *)
    | Assert of exp * exp list              (* assert(e); error msgs *)
    | Error of exp                          (* error(e); *)
    | Anno of spec list		            (* @assert or @loop_invariant *)
    | Markeds of stm Mark.marked            (* mark with source region info *)

  (* Variable declarations
  and vardecl =			    (* tp x; or tp x = e; *)
      VarDecl of ident * int * tp * exp option * ext *)
  (* reserve Ast.VarDecl for types *)
  (* define something new called SVarDecl for Function decl. *)
  (* need to define a new global Function decl. as well *)
  (* leave Ast.tp unchanged*)
  datatype svardecl =
      SVarDecl of ident * int * tp * exp option * ext

  (* datatype basicblock = Block of ident * tp * svardecl list * stm option * spec list
  
  type ssafunc = basicblock DA.array *)

  (* Global declarations *)
  datatype gdecl =
      Struct of ident * field list option * bool * ext
                                (* struct s; or struct s {...}; *)
    | TypeDef of ident * tp * ext (* typedef tp aid *)
    | FunTypeDef of ident * tp * vardecl list * spec list * ext
                                (* typedef rtp ftpname(tp1 x1, ..., tpn xn); *)
                                (* specs = pre/postconditions *)
    | Function of ident * tp * vardecl list * stm option
                  * spec list * bool * ext
                                (* rtp g(tp1 x1, ..., tpn xn); or *)
                                (* rtp g(tp1 x1, ..., tpn xn) { body } *)
                                (* specs = pre/postconditions, bool = is_external *)
    | Pragma of pragma * ext	(* #<pragma> ... *)

  (* Fields of structs *)
  datatype field =
      Field of ident * tp * ext	(* tp f; *)

  (* Specs (for contracts) *)
  datatype spec =
      Requires of exp * ext	 (* @requires *)
    | Ensures of exp * ext	 (* @ensures *)
    | LoopInvariant of exp * ext (* @loop_invariant *)
    | Assertion of exp * ext	 (* @assert *)


  (* Programs *)
  type program = gdecl list

  (* Printing C0 source, with redundant parentheses
   * and some syntactic sugar expanded *)
  structure Print =
  struct

    (* indent n str = str', only to be used for string
     * at beginning of line.  Used to make output more readable. *)
    fun indent n str = (StringCvt.padLeft #" " n "") ^ str

    fun pp_ident id = Symbol.name id

    fun pp_oper oper = case oper of
        (* SUB => "[]" *) (* OpExp(SUB,[e1,e2]) printed as "e1[e2]" *)
        LOGNOT => "!"
      | COMPLEMENT => "~"
      | NEGATIVE => "-"
      | DEREF => "*"
      | TIMES => "*" | DIVIDEDBY => "/" | MODULO => "%"
      | PLUS => "+" | MINUS => "-"
      | SHIFTLEFT => "<<" | SHIFTRIGHT => ">>"
      | LESS => "<" | LEQ => "<=" | GREATER => ">" | GEQ => ">="
      | EQ => "==" | NOTEQ => "!="
      | AND => "&" | XOR => "^" | OR => "|"
      | LOGAND => "&&" | LOGOR => "||"
      (* COND => "?:" *) (* OpExp(COND,[e1,e2,e3]) printed as "e1 ? e2 : e3" *)

    fun pp_tp (Int) = "int"
      | pp_tp (Bool) = "bool"
      | pp_tp (String) = "string"
      | pp_tp (Char) = "char"
      | pp_tp (Pointer(tp)) = pp_tp tp ^ "*"
      | pp_tp (Array(tp)) = pp_tp tp ^ "[]" (* in C: pp_tp tp ^ "*" *)
      | pp_tp (StructName(s)) = "struct " ^ Symbol.name(s)
      | pp_tp (TypeName(t)) = Symbol.name(t)
      | pp_tp (FunTypeName(t)) = Symbol.name(t)
      | pp_tp (FunType(rtp,params)) = pp_tp rtp ^ "(" ^ pp_tps params ^ ")"
      | pp_tp (Void) = "void"
      | pp_tp (Any) = "$" (* should only be internal *)
    and pp_tps nil = ""
      | pp_tps (VarDecl(_,tp,_,_)::nil) = pp_tp tp
      | pp_tps (VarDecl(_,tp,_,_)::tps) = pp_tp tp ^ "," ^ pp_tps tps
   
    fun pp_exp (SVar(id)) = pp_ident id
      | pp_exp (IntConst(w)) = Word32Signed.toString w
      | pp_exp (StringConst(s)) = "\"" ^ String.toCString s ^ "\""
      | pp_exp (CharConst(c)) = "'" ^ C0Char.toC0String c ^ "'"
      | pp_exp (True) = "true"
      | pp_exp (False) = "false"
      | pp_exp (Null) = "NULL"
      | pp_exp (OpExp(SUB, [e1,e2])) =
          pp_exp e1 ^ "[" ^ pp_exp e2 ^ "]"
      | pp_exp (OpExp(COND, [e1,e2,e3])) =
          "(" ^ pp_exp e1 ^ " ? " ^ pp_exp e2 ^ " : " ^ pp_exp e3 ^ ")"
      | pp_exp (OpExp(oper, [e])) =
          pp_oper oper ^ "(" ^ pp_exp e ^ ")"
      | pp_exp (OpExp(oper, [e1,e2])) =
          "(" ^ pp_exp e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp e2 ^ ")"
      | pp_exp (Select(OpExp(DEREF, [e]),id)) = 
          (* ( *e).f ===> e->f *)
          (* Should always be safe, as -> is the lowest-precedence operator...
           * -rjs nov 16 2012 *)
          pp_exp e ^ "->" ^ pp_ident id
      | pp_exp (Select(e,id)) = 
          "(" ^ pp_exp e ^ ")" ^ "." ^ pp_ident id
      | pp_exp (FunCall(id, es)) =
          pp_ident id ^ "(" ^ pp_exps es ^ ")"
      | pp_exp (AddrOf(id)) =
          "&" ^ pp_ident id
      | pp_exp (Invoke(e, es)) =
          "(" ^ pp_exp e ^ ")" ^ "(" ^ pp_exps es ^ ")"
      | pp_exp (Alloc(tp)) = "alloc" ^ "(" ^ pp_tp tp ^ ")"
      | pp_exp (AllocArray(tp, exp)) = "alloc_array" ^ "(" ^ pp_tp tp ^ ", " ^ pp_exp exp ^ ")"
      | pp_exp (Cast(tp, exp)) = "(" ^ "(" ^ pp_tp tp ^ ")" ^ pp_exp exp ^ ")"
      | pp_exp (Result) = "\\result"
      | pp_exp (Length(exp)) = "\\length" ^ "(" ^ pp_exp exp ^ ")"
      | pp_exp (Hastag(tp,exp)) = "\\hastag" ^ "(" ^ pp_tp tp ^ "," ^ pp_exp exp ^ ")"
      | pp_exp (Marked(marked_exp)) =
          pp_exp (Mark.data marked_exp)

    and pp_exps nil = ""
      | pp_exps (e::nil) = pp_exp e
      | pp_exps (e::es) = pp_exp e ^ ", " ^ pp_exps es

    fun pp_stm n (Assign (NONE, lv, e)) =
          indent n (pp_exp lv ^ " = " ^ pp_exp e ^ ";")
      | pp_stm n (Assign (SOME(oper), lv, e)) =
          indent n (pp_exp lv ^ " " ^ pp_oper oper ^ "= " ^ pp_exp e ^ ";")
      | pp_stm n (Exp(e)) =
          indent n (pp_exp e ^ ";")
      | pp_stm n (Seq([], [])) = (* eliminated special case? *)
          indent n "{ }"
      | pp_stm n (Seq(ds, ss)) =
          indent n "{\n"
          ^ pp_decls (n+2) ds
          ^ pp_stms (n+2) ss
          ^ indent n "}"
      | pp_stm n (StmDecl(d)) =
          pp_decls n [d]
      | pp_stm n (If(e, s1, s2)) =
        indent n ("if (" ^ pp_exp e ^ ") {\n")
        ^ pp_seq (n+2) s1
        ^ indent n "} else {\n"
        ^ pp_seq (n+2) s2
        ^ indent n "}"
      | pp_stm n (While(e, nil, s)) = (* no loop invariants *)
        indent n ("while (" ^ pp_exp e ^ ") {\n")
        ^ pp_seq (n+2) s
        ^ indent n "}"
      | pp_stm n (While(e, invs, s)) =
        indent n ("while (" ^ pp_exp e ^ ")\n")
        ^ pp_specs (n+2) invs
        ^ indent (n+2) "{\n"
        ^ pp_seq (n+4) s
        ^ indent (n+2) "}"
      | pp_stm n (For(s1, e, s2, nil, s3)) = (* no loop invariants *)
        indent n ("for (" ^ pp_simp_null s1 ^ "; " ^ pp_exp e ^ "; " ^ pp_simp_null s2 ^ ") {\n")
        ^ pp_seq (n+2) s3
        ^ indent n "}"
      | pp_stm n (For(s1, e, s2, invs, s3)) =
        indent n ("for (" ^ pp_simp_null s1 ^ "; " ^ pp_exp e ^ "; " ^ pp_simp_null s2 ^ ")\n")
        ^ pp_specs (n+2) invs
        ^ indent (n+2) "{\n"
        ^ pp_seq (n+4) s3
        ^ indent (n+2) "}"
      | pp_stm n (Continue) = indent n "continue;"
      | pp_stm n (Break) = indent n "break;"
      | pp_stm n (Return(SOME(e))) =
        indent n "return " ^ pp_exp e ^ ";"
      | pp_stm n (Return(NONE)) =
        indent n "return;"
      | pp_stm n (Assert(e1, e2s)) = (* drop error msgs *)
        indent n "assert(" ^ pp_exp e1 ^ ");"
      | pp_stm n (Error(e)) = (* drop error msgs *)
        indent n "error(" ^ pp_exp e ^ ");"
      | pp_stm n (Anno(specs)) = pp_specs n specs
      | pp_stm n (Markeds(marked_stm)) =
          pp_stm n (Mark.data marked_stm)

    and pp_simp_null (Seq(nil,nil)) = ""
      | pp_simp_null (Assign(NONE,lv,e)) =
           pp_exp lv ^ " = " ^ pp_exp e
      | pp_simp_null (Assign (SOME(oper), lv,e)) =
          pp_exp lv ^ " " ^ pp_oper oper ^ "= " ^ pp_exp e
      | pp_simp_null (Exp(e)) = pp_exp e
      | pp_simp_null (StmDecl(d)) = pp_simp_decl d
      | pp_simp_null (Markeds(marked_stm)) =
          pp_simp_null (Mark.data marked_stm)

    and pp_stms n nil = ""
      | pp_stms n (Anno(specs)::ss) = (* specs are terminated in newline *)
          pp_specs n specs ^ pp_stms n ss
      | pp_stms n (Seq([],ss1)::nil) = (* avoid spurious blocks *)
          pp_stms n ss1
      | pp_stms n (Markeds(marked_stm)::ss) =
          pp_stms n (Mark.data marked_stm::ss)
      | pp_stms n (s::ss) = pp_stm n s ^ "\n" ^ pp_stms n ss

    (* printing sequences where outer braces are already present *)
    and pp_seq n (Seq(ds,ss)) =
          pp_decls n ds ^ pp_stms n ss
      | pp_seq n (Markeds(marked_stm)) =
          pp_seq n (Mark.data marked_stm)
      | pp_seq n s =
          pp_stm n s ^ "\n"

    and pp_spec n (Requires(e, _)) = indent n ("//@requires " ^ pp_exp e ^ ";\n")
      | pp_spec n (Ensures(e, _)) = indent n ("//@ensures " ^ pp_exp e ^ ";\n")
      | pp_spec n (LoopInvariant(e, _)) = indent n ("//@loop_invariant " ^ pp_exp e ^ ";\n")
      | pp_spec n (Assertion(e, _)) = indent n ("//@assert " ^ pp_exp e ^ ";\n")

    and pp_specs n nil = ""
      | pp_specs n (spec::specs) = pp_spec n spec ^ pp_specs n specs

    (* pp_simp_decl, no semicolon here *)
    and pp_simp_decl (VarDecl(id, tp, NONE, ext)) =
          pp_tp tp ^ " " ^ pp_ident id
      | pp_simp_decl (VarDecl(id, tp, SOME(e), ext)) =
          pp_tp tp ^ " " ^ pp_ident id ^ " = " ^ pp_exp e

    and pp_decls n nil = ""
      | pp_decls n (d::decls) =
        indent n (pp_simp_decl d ^ ";\n")
        ^ pp_decls n decls

    fun pp_params nil = ""
      | pp_params (d::nil) = pp_simp_decl d
      | pp_params (d::params) = (* params <> nil *)
          pp_simp_decl d ^ ", " ^ pp_params params

    fun pp_fields (nil) = ""
      | pp_fields (Field(f,tp,ext)::fields) =
        indent 2 (pp_tp tp ^ " " ^ Symbol.name(f) ^ ";\n")
        ^ pp_fields fields

    fun pp_gdecl (Struct(s,NONE,_,ext)) =
        "struct " ^ Symbol.name(s) ^ ";\n"
      | pp_gdecl (Struct(s,SOME(fields),_,ext)) =
        "struct " ^ Symbol.name(s) ^ " {\n"
        ^ pp_fields fields ^ "};\n"
      | pp_gdecl (Function(fun_name, result, params, NONE, nil, is_extern, ext)) =
        (* no pre/postconditions *)
        (* (if is_extern then "extern " else "") *)
        pp_tp result ^ " " ^ pp_ident fun_name ^ "(" ^ pp_params params ^ ");\n"
      | pp_gdecl (Function(fun_name, result, params, NONE, specs, is_extern, ext)) =
        (* (if is_extern then "extern " else "") *)
        pp_tp result ^ " " ^ pp_ident fun_name ^ "(" ^ pp_params params ^ ")\n"
        ^ pp_specs 2 specs (* pre/postconditions, terminated by newline *)
        ^ indent 2 ";\n"
      | pp_gdecl (Function(fun_name, result, params, SOME(s), nil, is_extern, ext)) =
        "\n" ^ pp_tp result ^ " " ^ pp_ident fun_name ^ "("
        ^ pp_params params ^ ") {\n"
        ^ pp_seq 2 s
        ^ "}\n"
      | pp_gdecl (Function(fun_name, result, params, SOME(s), specs, is_extern, ext)) =
        "\n" ^ pp_tp result ^ " " ^ pp_ident fun_name ^ "(" ^ pp_params params ^ ")\n"
        ^ pp_specs 0 specs
        ^ "{\n" ^ pp_seq 2 s ^ "}\n"
      | pp_gdecl (TypeDef(aid, tp, ext)) =
        "typedef " ^ pp_tp tp ^ " " ^ Symbol.name aid ^ ";\n"
      | pp_gdecl (FunTypeDef(fid, rtp, params, nil, ext)) =
        "\n" ^ "typedef" ^ pp_tp rtp ^ " " ^ pp_ident fid ^ "(" ^ pp_params params ^ ");\n"
      | pp_gdecl (FunTypeDef(fid, rtp, params, specs, ext)) = (* specs <> nil *)
        "\n" ^ "typedef" ^ pp_tp rtp ^ " " ^ pp_ident fid ^ "(" ^ pp_params params ^ ")\n"
        ^ pp_specs 0 specs
        ^ indent 2 ";\n"
      | pp_gdecl (Pragma(UseLib(libname, _), ext)) =
        "#use <" ^ libname ^ ">\n"
      | pp_gdecl (Pragma(UseFile(filename, _), ext)) =
        "#use \"" ^ filename ^ "\"\n"
      | pp_gdecl (Pragma(Raw(pname, pargs), ext)) =
        pname ^ pargs ^ "\n"

    fun pp_gdecls nil = ""
      | pp_gdecls (gdecl::gdecls) =
          pp_gdecl gdecl ^ pp_gdecls gdecls

    val pp_stm = fn s => pp_stm 0 s

    fun pp_program (gdecls) =
        pp_gdecls gdecls

  end

end
