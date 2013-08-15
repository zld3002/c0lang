signature WARN =
sig
    val warn_program : Ast.program -> unit
end

structure Warn :> WARN =
struct

  structure A = Ast

    val max_col = 80
    val min_indent = 2

    (* lines and colums start at 1! *)
    fun line1 NONE = 0
      | line1 (SOME((l1, _), _, _)) = l1
    fun col1 NONE = 0
      | col1 (SOME((_, c1), _, _)) = c1
    fun line2 NONE = 0
      | line2 (SOME(_, (l2,_), _)) = l2
    fun col2 NONE = 0
      | col2 (SOME(_, (_,c2), _)) = c2

    fun diff_line NONE ext = true
      | diff_line (SOME((prev_l1:int, _), _, _)) (SOME((l1, _), _, _)) = (prev_l1 <> l1)
      | diff_line (SOME _) NONE = (* possible? *)
        true

    fun is_block (A.Markeds(marked_stm)) =
          is_block (Mark.data marked_stm)
      | is_block (A.Seq _) = true
      | is_block _ = false

    fun same_line ext' ext = (line1 ext' = line1 ext)

    fun pp_bounds (left, right) = "[" ^ Int.toString left ^ "," ^ Int.toString right ^ "]"

    fun pp_pos (line,col) = "(" ^ Int.toString line ^ "," ^ Int.toString col ^ ")"

    fun pp_ext NONE = "?"
      | pp_ext (SOME((line1,col1),(line2,col2),filename)) =
        "[" ^ pp_pos(line1,col1) ^ "," ^ pp_pos(line2, col2) ^ "]"

    fun out_of_bounds col (left, right) =
        col < left orelse right < col

    fun oob col (left, right) =
        if left = right
        then "should start at column " ^ Int.toString left
             ^ "; starts at column " ^ Int.toString col
        else "should start in range [" ^ Int.toString left ^ ","
             ^ Int.toString right ^ "]; starts at column "
             ^ Int.toString col

    fun stm_ext (A.Markeds(marked_stm)) ext =
          stm_ext (Mark.data marked_stm) (Mark.ext marked_stm)
      | stm_ext (A.StmDecl(A.VarDecl(_, _, _, ext'))) ext =
        (* StmDecls are not provided a region *)
        ext'
      | stm_ext s ext = ext

    fun spec_ext (A.Requires(e, ext)) = ext
      | spec_ext (A.Ensures(e, ext)) = ext
      | spec_ext (A.LoopInvariant(e, ext)) = ext
      | spec_ext (A.Assertion(e, ext)) = ext

    fun gdecl_ext (A.Struct(_, _, _, ext)) = ext
      | gdecl_ext (A.Function(_, _, _, _, _, _, ext)) = ext
      | gdecl_ext (A.TypeDef(_, _, ext)) = ext
      | gdecl_ext (A.Pragma(_, ext)) = ext 

    (* indent n str = str', only to be used for string
     * at beginning of line.  Used to make output more readable. *)
    (*
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
      | pp_tp (Void) = "void"
      | pp_tp (Any) = "$" (* should only be internal *)
    *)

    (*
    fun pp_exp (Var(id)) = pp_ident id
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
      | pp_exp (Alloc(tp)) = "alloc" ^ "(" ^ pp_tp tp ^ ")"
      | pp_exp (AllocArray(tp, exp)) = "alloc_array" ^ "(" ^ pp_tp tp ^ ", " ^ pp_exp exp ^ ")"
      | pp_exp (Result) = "\\result"
      | pp_exp (Length(exp)) = "\\length" ^ "(" ^ pp_exp exp ^ ")"
      | pp_exp (Old(exp)) = "\\old" ^ "(" ^ pp_exp exp ^ ")"
      | pp_exp (Marked(marked_exp)) =
	  pp_exp (Mark.data marked_exp)
    *)
    fun indent_exp' e' left ext = () (* fix!!! *)

    and indent_exp (A.Marked(marked_exp)) bounds ext =
          indent_exp (Mark.data marked_exp) bounds (Mark.ext marked_exp)
      | indent_exp e bounds ext =
        ( if out_of_bounds (col1 ext) bounds
          then ErrorMsg.warn ext
               ("expression not properly aligned\n" ^ oob (col1 ext) bounds)
          else ()
        ; indent_exp' e (col1 ext) ext )

    (*
    and pp_exps nil = ""
      | pp_exps (e::nil) = pp_exp e
      | pp_exps (e::es) = pp_exp e ^ ", " ^ pp_exps es
    *)

    fun indent_stm s bounds ext =
        let val ext' = stm_ext s ext
        in
            ( if out_of_bounds (col1 ext') bounds
              then ErrorMsg.warn ext' ("statement not properly aligned\n" ^ oob (col1 ext') bounds )
              else ()
            ; indent_stm' s (col1 ext') ext' )
        end

    and indent_block s bounds ext =
        if is_block s andalso same_line (stm_ext s ext) ext
        then indent_seq s bounds ext
        else indent_stm s bounds ext

    and indent_else s bounds then_ext ext =
        if is_block s andalso line2 then_ext = line1 (stm_ext s ext)
        then (* continuing on the 'else' line *)
            indent_seq s bounds then_ext
        else indent_stm s bounds ext (* insist on just as then-case? *)

    (* indent_stm' s left ext
     * have already checked s is properly aligned; check substatements
     * or expressions *)
    and indent_stm' (A.Assign (_, lv, e)) left ext =
        (* lv must be indented to column 'left' *)
          indent_exp e (left + min_indent, max_col) ext
          (* (pp_exp lv ^ " = " ^ pp_exp e ^ ";") *)
      | indent_stm' (A.Exp(e)) left ext =
        (* e must be indented to column 'left' *)
          indent_exp' e left ext
      | indent_stm' (A.Seq([], [])) left ext = (* eliminated special case? *)
	  ()
      | indent_stm' (A.Seq(ds, ss)) left ext =
          indent_seq (A.Seq(ds, ss)) (left + min_indent, max_col) ext
      | indent_stm' (A.StmDecl(d)) left ext =
          ignore (indent_decls [d] (left, max_col) NONE) (* do not increase indent *)
      | indent_stm' (A.If(e, s1, s2)) left ext =
        (* indent n ("if (" ^ pp_exp e ^ ") {\n")
	   ^ pp_seq (n+2) s1
	   ^ indent n "} else {\n"
	   ^ pp_seq (n+2) s2
	   ^ indent n "}"
         *)
        ( indent_exp e (left + min_indent, max_col) ext (* ?? *)
        ; indent_block s1 (left + min_indent, max_col) ext
          (* cannot check the 'else' placement, since region info is lost *)
        ; indent_else s2 (left + min_indent, max_col) (stm_ext s1 ext) ext )
      | indent_stm' (A.While(e, nil, s)) left ext = (* no loop invariants *)
        (* indent n ("while (" ^ pp_exp e ^ ") {\n")
 	   ^ pp_seq (n+2) s
	   ^ indent n "}"
         *)
        ( indent_exp e (left + min_indent, max_col) ext (* ?? *)
        ; indent_stm s (left + min_indent, max_col) ext )
      | indent_stm' (A.While(e, invs, s)) left ext =
        (*
	indent n ("while (" ^ pp_exp e ^ ")\n")
	^ pp_specs (n+2) invs
	^ indent (n+2) "{\n"
	^ pp_seq (n+4) s
	^ indent (n+2) "}"
        *)
        ( indent_exp e (left + min_indent, max_col) ext 
        ; ignore (indent_specs invs (left + min_indent, max_col)) (* fix!!! *)
        ; indent_stm s (left + min_indent, max_col) ext )
      | indent_stm' (A.For(s1, e, s2, nil, s3)) left ext = (* no loop invariants *)
        (*
	indent n ("for (" ^ pp_simp_null s1 ^ "; " ^ pp_exp e ^ "; " ^ pp_simp_null s2 ^ ") {\n")
	^ pp_seq (n+2) s3
	^ indent n "}"
        *)
        ( indent_stm s3 (left + min_indent, max_col) ext )
      | indent_stm' (A.For(s1, e, s2, invs, s3)) left ext =
        (*
	indent n ("for (" ^ pp_simp_null s1 ^ "; " ^ pp_exp e ^ "; " ^ pp_simp_null s2 ^ ")\n")
	^ pp_specs (n+2) invs
	^ indent (n+2) "{\n"
	^ pp_seq (n+4) s3
	^ indent (n+2) "}"
        *)
        ( ignore(indent_specs invs (left + min_indent, max_col))
        ; indent_stm s3 (left + min_indent, max_col) ext )
      | indent_stm' (A.Continue) left ext = ()
      | indent_stm' (A.Break) left ext = ()
      | indent_stm' (A.Return(SOME(e))) left ext =
	(* indent n "return " ^ pp_exp e ^ ";" *)
        ( indent_exp e (left + min_indent, max_col) ext )
      | indent_stm' (A.Return(NONE)) left ext = ()
      | indent_stm' (A.Assert(e1, e2s)) left ext = (* drop error msgs *)
        ( indent_exp e1 (left + min_indent, max_col) ext )
        (* indent n "assert(" ^ pp_exp e1 ^ ");" *)
      | indent_stm' (A.Error(e)) left ext = (* drop error msgs *)
        ( indent_exp e (left + min_indent, max_col) ext )
        (* indent n "error(" ^ pp_exp e ^ ");" *)
      | indent_stm' (A.Anno(specs)) left ext =
        ignore (indent_specs specs (left + min_indent, max_col))
      | indent_stm' (A.Markeds(marked_stm)) left ext =
	  indent_stm' (Mark.data marked_stm) left (Mark.ext marked_stm)

    (*
    and indent_simp_null (Seq(nil,nil)) = ""
      | indent_simp_null (Assign(NONE,lv,e)) =
	   indent_exp lv ^ " = " ^ indent_exp e
      | indent_simp_null (Assign (SOME(oper), lv,e)) =
	  indent_exp lv ^ " " ^ indent_oper oper ^ "= " ^ indent_exp e
      | indent_simp_null (Exp(e)) = indent_exp e
      | indent_simp_null (StmDecl(d)) = indent_simp_decl d
      | indent_simp_null (Markeds(marked_stm)) =
	  indent_simp_null (Mark.data marked_stm)
   *)

    and indent_stms nil bounds prev_ext ext = ()
      | indent_stms (A.Anno(specs)::ss) bounds prev_ext ext =
	let val bounds' = indent_specs specs bounds
        in
            indent_stms ss bounds' NONE ext (* fix!!! *)
        end
      | indent_stms (A.Seq(ds',ss')::ss) bounds prev_ext ext =
        (* sequence without region means implicit block due
         * to declaration in middle of block.  Treat this case
         * as if there was no block
         *)
        let val (bounds', prev_ext') = indent_decls ds' bounds prev_ext
        in
            indent_stms (ss' @ ss) bounds' prev_ext' ext
        end
      | indent_stms (s::ss) bounds prev_ext ext = 
        let val ext' = stm_ext s ext
            val next_bounds = if diff_line prev_ext ext'
                              then (col1 ext', col1 ext')
                              else bounds
            (* val () = print (pp_ext ext' ^ "\n") *)
            (* val () = print (pp_bounds bounds ^ "\n") *)
        in ( if diff_line prev_ext ext' andalso out_of_bounds (col1 ext') bounds
             then ErrorMsg.warn ext' ("statement not properly aligned\n" ^ oob (col1 ext') bounds)
             else ()
           (* ; print ("'s" ^ Int.toString (col1 ext') ^ "\n" ^ A.Print.pp_stm s ^ "\n") *)
           ; indent_stm' s (col1 ext') ext' (* check substatements and subexpressions *)
           ; indent_stms ss next_bounds ext' ext )
        end 

    and indent_seq (A.Seq(ds, ss)) bounds ext =
        let val (bounds', last_ext) = indent_decls ds bounds NONE (* no prior statement in list *)
        in indent_stms ss bounds' last_ext ext end
      | indent_seq (A.Markeds(marked_stm)) bounds ext =
	  indent_seq (Mark.data marked_stm) bounds (Mark.ext marked_stm)
      | indent_seq s bounds ext = (* possible?  allowed? *)
	  indent_stm s bounds ext

    and indent_spec (A.Requires(e, ext)) left = indent_exp e (left+2, max_col) ext
      | indent_spec (A.Ensures(e, ext)) left = indent_exp e (left+2, max_col) ext
      | indent_spec (A.LoopInvariant(e, ext)) left = indent_exp e (left+2, max_col) ext
      | indent_spec (A.Assertion(e, ext)) left = indent_exp e (left+2, max_col) ext

    and indent_specs nil bounds = bounds
      | indent_specs (spec::specs) bounds =
        let val left = col1 (spec_ext spec)
        in 
            ( if out_of_bounds left bounds
              then ErrorMsg.warn (spec_ext spec)
                                 ("contract annotation not properly aligned\n" ^ oob left bounds)
              else ()
            ; indent_spec spec left
            ; indent_specs specs (left, left) )
        end

    (* layout_simp_decl, no semicolon here *)
    (*
    and layout_simp_decl (VarDecl(id, tp, NONE, ext)) =
	  layout_tp tp ^ " " ^ layout_ident id
      | layout_simp_decl (VarDecl(id, tp, SOME(e), ext)) =
	  layout_tp tp ^ " " ^ layout_ident id ^ " = " ^ layout_exp e
    *)

    and indent_decls nil bounds prev_ext = (bounds, prev_ext)
      | indent_decls (A.VarDecl(id, tp, eOpt, ext)::decls) bounds prev_ext =
        (* ignore eOpt for now, fix!!! *)
        ( if diff_line prev_ext ext andalso out_of_bounds (col1 ext) bounds
          then ErrorMsg.warn ext
               ("variable declaration not properly aligned\n" ^ oob (col1 ext) bounds)
          else ()
        ; indent_decls decls (col1 ext, col1 ext) ext)

    (*
    fun layout_params nil = ""
      | layout_params (d::nil) = layout_simp_decl d
      | layout_params (d::params) = (* params <> nil *)
	  layout_simp_decl d ^ ", " ^ layout_params params
    *)

    fun indent_fields (nil) bounds = ()
      | indent_fields (A.Field(f,tp,ext)::fields) bounds =
        ( if out_of_bounds (col1 ext) bounds
          then ErrorMsg.warn ext
               ("field not properly aligned\n" ^ oob (col1 ext) bounds)
          else ()
        ; indent_fields fields (col1 ext, col1 ext) )
        (*
	indent 2 (layout_tp tp ^ " " ^ Symbol.name(f) ^ ";\n")
	^ layout_fields fields
        *)

    fun indent_gdecl (A.Struct(s,NONE,_,ext)) =
	(* "struct " ^ Symbol.name(s) ^ ";\n" *)
        ()
      | indent_gdecl (A.Struct(s,SOME(fields),_,ext)) =
        (*
	"struct " ^ Symbol.name(s) ^ " {\n"
	^ pp_fields fields ^ "};\n"
         *)
        indent_fields fields (col1 ext + min_indent, max_col)
      | indent_gdecl (A.Function(fun_name, result, params, NONE, nil, is_extern, ext)) =
	(* no pre/postconditions *)
	(* pp_tp result ^ " " ^ pp_ident fun_name ^ "(" ^ pp_params params ^ ");\n" *)
        ()
      | indent_gdecl (A.Function(fun_name, result, params, NONE, specs, is_extern, ext)) =
	(*
         pp_tp result ^ " " ^ pp_ident fun_name ^ "(" ^ pp_params params ^ ")\n"
	 ^ pp_specs 2 specs (* pre/postconditions, terminated by newline *)
	 ^ pp 2 ";\n"
        *)
        ignore (indent_specs specs (col1 ext + min_indent, max_col))
      | indent_gdecl (A.Function(fun_name, result, params, SOME(s), nil, is_extern, ext)) =
        (*
	"\n" ^ pp_tp result ^ " " ^ pp_ident fun_name ^ "("
	^ pp_params params ^ ") {\n"
	^ pp_seq 2 s
	^ "}\n"
        *)
        ignore (indent_seq s (col1 ext + min_indent, max_col) ext)
      | indent_gdecl (A.Function(fun_name, result, params, SOME(s), specs, is_extern, ext)) =
        (*
	"\n" ^ pp_tp result ^ " " ^ pp_ident fun_name ^ "(" ^ pp_params params ^ ")\n"
	^ pp_specs 0 specs
	^ "{\n" ^ pp_seq 2 s ^ "}\n"
        *)
        let val bounds' = indent_specs specs (col1 ext + min_indent, max_col)
        in
            ignore (indent_seq s bounds' ext)
        end
      | indent_gdecl (A.TypeDef(aid, tp, ext)) =
	(* "typedef " ^ pp_tp tp ^ " " ^ Symbol.name aid ^ ";\n" *)
        ()
      | indent_gdecl (A.Pragma(A.UseLib(libname, _), ext)) =
	(* "#use <" ^ libname ^ ">\n" *)
        ()
      | indent_gdecl (A.Pragma(A.UseFile(filename, _), ext)) =
	(* "#use \"" ^ filename ^ "\"\n" *)
        ()
      | indent_gdecl (A.Pragma(A.Raw(pname, pargs), ext)) =
        (* pname ^ pargs ^ "\n" *)
        ()

    fun layout_gdecl (gdecl) =
        let val ext = gdecl_ext gdecl
            val () = if out_of_bounds (col1 ext) (1, 1)
                     then ErrorMsg.warn ext
                          ("top level declaration indented\n" ^ oob (col1 ext) (1,1))
                     else ()
            val () = indent_gdecl gdecl
        in
            ()
        end

    fun layout_gdecls nil = ()
      | layout_gdecls (gdecl::gdecls) =
        ( layout_gdecl gdecl
        ; layout_gdecls gdecls )

    fun warn_program (gdecls) = layout_gdecls gdecls


end (* structure Warn *)
