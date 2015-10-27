(* C0 Compiler
 * Warnings for proper indentation and alignment
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature WARN =
sig
    val warn_program : Ast.program -> unit  (* prints all warnings *)
end

(*
 * 'bounds' refers to an interval [left,right]
 * at present, bounds are always [left,left] for exact alignment
 * or [left,max_col] when only a minimum indentation is required
 *
 * 'left' refers to the column of an enclosing
 * statement or expression
 *
 * 'ext' refers to an "extent" which is either NONE when there
 * is no information available, or has the form
 * SOME((line1, col1), (line2, col2), filename)
 *
 * The style criteria are described in a separate file, syntaxrules.txt
 *)

structure Warn :> WARN =
struct

  structure A = Ast

    val max_col = 80            (* max column permitted *)
    val min_indent = 2          (* minimum indent required *)

    (* extraction line or column information from ext *)
    (* lines and colums start at 1 *)
    fun line1 NONE = 0
      | line1 (SOME((l1, _), _, _)) = l1
    fun col1 NONE = 0
      | col1 (SOME((_, c1), _, _)) = c1
    fun line2 NONE = 0
      | line2 (SOME(_, (l2,_), _)) = l2
    fun col2 NONE = 0
      | col2 (SOME(_, (_,c2), _)) = c2

    (* diff_line ext ext' = true if ext and ext' start on different lines *)
    fun diff_line NONE ext = true
      | diff_line (SOME((prev_l1:int, _), _, _)) (SOME((l1, _), _, _)) =
          (prev_l1 <> l1)
      | diff_line (SOME _) NONE = (* possible? *)
        true

    fun is_block (A.Markeds(marked_stm)) =
          is_block (Mark.data marked_stm)
      | is_block (A.Seq _) = true
      | is_block _ = false

    fun is_marked (A.Markeds(marked_stm)) = true
      | is_marked _ = false

    fun is_if (A.Markeds(marked_stm)) =
          is_if (Mark.data marked_stm)
      | is_if (A.If _) = true
      | is_if _ = false

    (* debugging functions *)
    fun pp_bounds (left, right) = "[" ^ Int.toString left ^ "," ^ Int.toString right ^ "]"

    fun pp_pos (line,col) = "(" ^ Int.toString line ^ "," ^ Int.toString col ^ ")"

    fun pp_ext NONE = "?"
      | pp_ext (SOME((line1,col1),(line2,col2),filename)) =
        "[" ^ pp_pos(line1,col1) ^ "," ^ pp_pos(line2, col2) ^ "]"

    (* out_of_bounds col (left, right) = true
     * if col is out of bounds wrt region [left, right].
     * Special consideration are applied when lines are too long *)
    fun out_of_bounds col (left, right) =
        (* col = 0 means no information available
         * do not declare out of bounds.  Similarly,
         * if col or left bound are > max_col, suppress
         * error message *)
        (0 < col andalso col <= max_col)
        andalso (0 < left andalso left <= max_col)
        andalso (col < left orelse right < col)

    (* oob col (left, right) = msg, the warning message if
     * 'col' is out of bounds [left,right] *)
    fun oob col (left, right) =
        if left = right
        then "should start at column " ^ Int.toString left
             ^ "; starts at column " ^ Int.toString col
        else "should start in range [" ^ Int.toString left ^ ","
             ^ Int.toString right ^ "]; starts at column "
             ^ Int.toString col

    (* stm_ext' s ext = ext', the extent of s or ext' if not provided *)
    fun stm_ext' (A.Markeds(marked_stm)) ext =
          stm_ext' (Mark.data marked_stm) (Mark.ext marked_stm)
      | stm_ext' (A.StmDecl(A.VarDecl(_, _, _, ext'))) ext =
        (* StmDecls are not marked by a region but carry it *)
        ext'
      | stm_ext' s ext = ext

    (* stm_ext s = ext, the extent of s or NONE if not provided *)
    fun stm_ext (A.Markeds(marked_stm)) =
          stm_ext' (Mark.data marked_stm) (Mark.ext marked_stm)
      | stm_ext s = stm_ext' s NONE

    fun exp_ext (A.Marked(marked_exp)) ext =
          exp_ext (Mark.data marked_exp) (Mark.ext marked_exp)
      | exp_ext e ext = ext (* require there to be a mark? *)

    fun spec_ext (A.Requires(e, ext)) = ext
      | spec_ext (A.Ensures(e, ext)) = ext
      | spec_ext (A.LoopInvariant(e, ext)) = ext
      | spec_ext (A.Assertion(e, ext)) = ext

    fun gdecl_ext (A.Struct(_, _, _, ext)) = ext
      | gdecl_ext (A.TypeDef(_, _, ext)) = ext
      | gdecl_ext (A.FunTypeDef(_, _, _, _, ext)) = ext
      | gdecl_ext (A.Function(_, _, _, _, _, _, ext)) = ext
      | gdecl_ext (A.Pragma(_, ext)) = ext 

    (* currently not checking types *)
    (*
    fun indent_tp (Int) = ()
      | indent_tp (Bool) = ()
      | indent_tp (String) = ()
      | indent_tp (Char) = ()
      | indent_tp (Pointer(tp)) = indent_tp tp
      | indent_tp (Array(tp)) = indent_tp tp
      | indent_tp (StructName(s)) = ()
      | indent_tp (TypeName(t)) = ()
      | indent_tp (Void) = ()
      | indent_tp (Any) = ()
    *)

    fun indent_exp' (A.Var(id)) left ext = ()
      | indent_exp' (A.IntConst(w)) left ext = ()
      | indent_exp' (A.StringConst(s)) left ext = ()
      | indent_exp' (A.CharConst(c)) left ext = ()
      | indent_exp' (A.True) left ext = ()
      | indent_exp' (A.False) left ext = ()
      | indent_exp' (A.Null) left ext = ()
      | indent_exp' (A.OpExp(A.SUB, [e1,e2])) left ext =
        (* force same line? *)
        ( indent_exp' e1 left ext
        ; indent_exp e2 (left + 0, max_col) ext )
      | indent_exp' (A.OpExp(A.COND, [e1,e2,e3])) left ext =
        ( indent_exp' e1 left ext 
        ; if diff_line (exp_ext e2 ext) (exp_ext e3 ext) (* working??? *)
          then indent_exps [e2,e3] (left + 0, max_col) (exp_ext e2 ext) ext
          else ( indent_exp e2 (left + 0, max_col) ext
               ; indent_exp e3 (left + 0, max_col) ext )
        ) 
      | indent_exp' (A.OpExp(oper, [e])) left ext =
          (* increase indent only by 1, in case 'e' on same line as 'oper' *)
          indent_exp e (left + 0, max_col) ext
      | indent_exp' (A.OpExp(oper, [e1,e2])) left ext =
        ( indent_exp' e1 left ext
        ; indent_exp e2 (left + 0, max_col) ext )
      | indent_exp' (A.Select(A.OpExp(A.DEREF, [e]),id)) left ext = 
          indent_exp' e left ext  (* force same line? *)
      | indent_exp' (A.Select(e,id)) left ext = 
          indent_exp' e left ext  (* force same line? *)
      | indent_exp' (A.FunCall(id, es)) left ext =
          (* here we do force an increase --- seems too odd without *)
          indent_exps es (left + min_indent, max_col) NONE ext (* force same line? *)
      | indent_exp' (A.AddrOf(id)) left ext = (* force consecutive? *)
          ()
      | indent_exp' (A.Invoke(e, es)) left ext =
        ( indent_exp' e left ext
        ; indent_exps es (left + min_indent, max_col) NONE ext ) (* force same line? *)
      | indent_exp' (A.Alloc(tp)) left ext =
          ()
      | indent_exp' (A.AllocArray(tp, e)) left ext =
          (* here we do force an increase --- seems too odd without *)
          indent_exp e (left + min_indent, max_col) ext
      | indent_exp' (A.Cast(tp, e)) left ext =
          (* here we do force an increase --- seems too odd without *)
          indent_exp e (left + min_indent, max_col) ext
      | indent_exp' (A.Result) left ext = ()
      | indent_exp' (A.Length(e)) left ext = 
          (* here we do force an increase --- seems too odd without *)
          indent_exp e (left + min_indent, max_col) ext
      | indent_exp' (A.Hastag(tp, e)) left ext =
          (* here we do force an increase --- seems too odd without *)
          indent_exp e (left +  min_indent, max_col) ext
      | indent_exp' (A.Marked(marked_exp)) left ext =
	  indent_exp' (Mark.data marked_exp) left (Mark.ext marked_exp)

    and indent_exps nil bounds prev_ext ext = ()
      | indent_exps (e::es) bounds prev_ext ext =
        let val ext' = exp_ext e ext
            val next_bounds = if diff_line prev_ext ext'
                              then (col1 ext', col1 ext')
                              else bounds
        in
            ( if diff_line prev_ext ext' andalso out_of_bounds (col1 ext') bounds
              then ErrorMsg.warn ext'
                     ("expression sequence not properly aligned\n" ^ oob (col1 ext') bounds)
              else ()
            ; indent_exp' e (col1 ext') ext'
            ; indent_exps es next_bounds ext' ext )
        end

    and indent_exp (A.Marked(marked_exp)) bounds ext =
          indent_exp (Mark.data marked_exp) bounds (Mark.ext marked_exp)
      | indent_exp e bounds ext =
        ( if out_of_bounds (col1 ext) bounds
          then ErrorMsg.warn ext
                 ("expression not properly aligned\n" ^ oob (col1 ext) bounds)
          else ()
          (* instead of (col1 ext) we use #1 bounds as a loose
           * approximation to allow, for example
           * return true &&
           *   true;
           * as legal *)
        ; indent_exp' e (#1 bounds) ext )

    (* if not marked, do not analyze: position information unavailable *)
    (* currently used to handle expansion of lv++ to lv += 1 *)
    and indent_marked_exp (A.Marked(marked_exp)) bounds =
          indent_exp (Mark.data marked_exp) bounds (Mark.ext marked_exp)
      | indent_marked_exp e bounds = ()

    fun indent_stm s bounds ext =
        (* s should carry its own extent; accept if it does not *)
        let val ext' = stm_ext s
        in
            ( if out_of_bounds (col1 ext') bounds
              then ErrorMsg.warn ext'
                     ("statement not properly aligned\n" ^ oob (col1 ext') bounds)
              else ()
            ; indent_stm' s (col1 ext') ext' )
        end

    (* indent_block s bounds ext
     * used for then-branch of conditional or while/for loop body.
     * If it is an explicit block, ignore the '{' and '}' braces
     * and insist on proper indentation of statement sequence inside.
     *
     * Implicit blocks arise from '//@assert e;\n s' and need to be
     * treated like statements (indentation required if these constitute
     * a conditional branch)
     *)
    and indent_block s bounds ext =
        if is_block s andalso is_marked s (* require explicit braces *)
        then indent_seq s bounds ext
        else indent_stm s bounds ext

    (* indent_else s left bounds then_ext ext
     * like indent_block, but account for 'else if' which inherits
     * bounds from enclosing 'if' *)
    and indent_else s left bounds then_ext ext =
        (* s may not have a region, because it could be an implicit
         * else case, which explands to '{}', or '//@assert e;\n s' *)
        if is_block s andalso is_marked s (* require explicit braces *)
        then indent_seq s bounds then_ext
        else if is_if s
        then (* 'else if' uses bounds from enclosing 'if' *)
            indent_stm' s left (stm_ext s)
        else 
            indent_stm s bounds ext

    (* indent_stm' s left ext
     * check substatements and expressions of 's' for proper indentation.
     * 'left' is the column of 's', 'ext' an (approx) region for 's'.
     * 's' has already been checked *)
    and indent_stm' (A.Assign (_, lv, e)) left ext =
        (* lv must be indented to column 'left' *)
        (* probably should be checked if it is complex *)
        indent_marked_exp e (left + min_indent, max_col)
      | indent_stm' (A.Exp(e)) left ext =
        (* because the beginning of the expression 'e' is the same
         * as the beginning of the statement 'e;', we just check
         * the subexpressions of 'e', not 'e' itself *)
        indent_exp' e left ext
      | indent_stm' (A.Seq([], [])) left ext = ()
      | indent_stm' (A.Seq(ds, ss)) left ext =
          indent_seq (A.Seq(ds, ss)) (left + min_indent, max_col) ext
      | indent_stm' (A.StmDecl(d)) left ext =
        (* do not increase indent; no prior extent in a sequence *)
        ignore (indent_decls [d] (left, max_col) NONE)
      | indent_stm' (A.If(e, s1, s2)) left ext =
        let val bounds = (left + min_indent, max_col)
            val () = indent_exp e bounds ext
            val () = indent_block s1 bounds ext
            (* cannot check the 'else' placement, since region info is lost *)
            val () = indent_else s2 left (left + min_indent, max_col) (stm_ext s1) ext
        in () end
      | indent_stm' (A.While(e, invs, s)) left ext =
        let val bounds = (left + min_indent, max_col)
            val () = indent_exp e bounds ext 
            val () = indent_specs invs bounds
            val () = indent_block s bounds ext
        in () end
      | indent_stm' (A.For(s1, e, s2, invs, s3)) left ext =
        (* treat '(s1; e; s2)' like a sequence of statements *)
        let val bounds = (left + min_indent, max_col)
            val s_e = A.Markeds(Mark.mark'(A.Exp(e), exp_ext e ext))
            val () = indent_stms [s1, s_e, s2] bounds NONE ext
            val () = indent_specs invs bounds
            val () = indent_block s3 bounds ext
        in () end
      | indent_stm' (A.Continue) left ext = ()
      | indent_stm' (A.Break) left ext = ()
      | indent_stm' (A.Return(SOME(e))) left ext =
          indent_exp e (left + min_indent, max_col) ext
      | indent_stm' (A.Return(NONE)) left ext = ()
      | indent_stm' (A.Assert(e1, e2s)) left ext = (* drop error msgs *)
          indent_exp e1 (left + min_indent, max_col) ext
      | indent_stm' (A.Error(e)) left ext =
          indent_exp e (left + min_indent, max_col) ext
      | indent_stm' (A.Anno(specs)) left ext =
          indent_specs specs (left + min_indent, max_col)
      | indent_stm' (A.Markeds(marked_stm)) left ext =
	  indent_stm' (Mark.data marked_stm) left (Mark.ext marked_stm)

    (* indent_stms ss bounds prev_ext ext
     * check sequence 'ss' according to 'bounds'.
     * 'prev_ext' is the region of the previous statement (before 'ss')
     * or NONE if there is none; 'ext' is the enclosing region of 'ss'
     *)
    and indent_stms nil bounds prev_ext ext = ()
      | indent_stms (A.Anno(specs)::ss) (left, right) prev_ext ext =
	let val loose_bounds = (left+3, max_col) (* '//@' is 3 characters *)
            val () = indent_specs specs loose_bounds
        (* cannot reliably tell real indentation of specs *)
        (* use previous bounds *)
        in
            indent_stms ss (left, right) prev_ext ext
        end
      | indent_stms (A.Seq(ds',ss')::ss) bounds prev_ext ext =
        (* sequence without region information means implicit block
         * due to a declaration in middle of a block.  Treat this case
         * as if there was no block.
         *)
        let val (bounds', prev_ext') = indent_decls ds' bounds prev_ext
        in
            indent_stms (ss' @ ss) bounds' prev_ext' ext
        end
      | indent_stms (s::ss) bounds prev_ext ext = 
        let val ext' = stm_ext s
            val next_bounds = if diff_line prev_ext ext'
                              then (col1 ext', col1 ext')
                              else bounds
        in ( if diff_line prev_ext ext' andalso out_of_bounds (col1 ext') bounds
             then ErrorMsg.warn ext'
                    ("statement not properly aligned\n" ^ oob (col1 ext') bounds)
             else ()
           ; indent_stm' s (col1 ext') ext' (* check substatements and subexpressions of 's' *)
           ; indent_stms ss next_bounds ext' ext )
        end 

    (* indent_seq s bounds ext
     * check statements inside sequence 's' according to 'bounds',
     * 'ext' is extent of 's'.
     * See indent_stms *)
    and indent_seq (A.Seq(ds, ss)) bounds ext =
        let
            val (bounds', last_ext) = indent_decls ds bounds NONE (* no prior statement in list *)
        in
            indent_stms ss bounds' last_ext ext
        end
      | indent_seq (A.Markeds(marked_stm)) bounds ext =
	  indent_seq (Mark.data marked_stm) bounds (Mark.ext marked_stm)
      | indent_seq s bounds ext = (* should be impossible *)
	  indent_stm s bounds ext

    (* indent_spec spec left
     * check indentation of subexpression of 'spec', where 'left'
     * is the indentation of 'spec'.  Note that '//@' does not count
     * into the region or indentation of a specification *)
    and indent_spec (A.Requires(e, ext)) left = indent_exp e (left + min_indent, max_col) ext
      | indent_spec (A.Ensures(e, ext)) left = indent_exp e (left + min_indent, max_col) ext
      | indent_spec (A.LoopInvariant(e, ext)) left = indent_exp e (left + min_indent, max_col) ext
      | indent_spec (A.Assertion(e, ext)) left = indent_exp e (left + min_indent, max_col) ext

    (* indent_specs specs bounds
     * check indentation of 'specs' with respect to 'bounds'.
     * We cannot reliably tell where the pseudo-comment for an annotation starts
     * so we force the alignment to be internally consistent, but do not return
     * bounds information *)
    and indent_specs nil bounds = ()
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

    (* indent_decls ds bounds prev_ext = (bounds', last_ext)
     * check indentation of 'ds' with respect to 'bounds'.
     * 'prev_ext' is the extent of the previous declaration before
     * 'ds' or NONE.
     * Returns new bounds and the region for the last declaration
     * in 'ds' so that the alignment of statements following 'ds'
     * can be enforced *)
    and indent_decls nil bounds prev_ext = (bounds, prev_ext)
      | indent_decls (A.VarDecl(id, tp, eOpt, ext)::decls) (bounds as (left,right)) prev_ext =
        ( if diff_line prev_ext ext andalso out_of_bounds (col1 ext) bounds
          then ErrorMsg.warn ext
                 ("variable declaration not properly aligned\n" ^ oob (col1 ext) bounds)
          else ()
        ; (case eOpt
            of NONE => ()
             | SOME(e) => indent_marked_exp e (left + min_indent, max_col))
        ; indent_decls decls (col1 ext, col1 ext) ext)

    (* currently not checking indentation of function parameters; probably should *)
    (*
     fun indent_params ds bounds = ignore (indent_decls ds bounds NONE)
    *)

    (* indent_fields fields bounds
     * check indentation of 'fields' wrt 'bounds'.
     * After the first one, the remaining ones must align exactly
     * on the left column *)
    fun indent_fields (nil) bounds = ()
      | indent_fields (A.Field(f,tp,ext)::fields) bounds =
        ( if out_of_bounds (col1 ext) bounds
          then ErrorMsg.warn ext
                 ("field not properly aligned\n" ^ oob (col1 ext) bounds)
          else ()
        ; indent_fields fields (col1 ext, col1 ext) )

    (* indent_gdecl' gdecl
     * check indentation of components of 'gdecl' *)
    fun indent_gdecl' (A.Struct(s,NONE,_,ext)) = ()
      | indent_gdecl' (A.Struct(s,SOME(fields),_,ext)) =
          indent_fields fields (col1 ext + min_indent, max_col)
      | indent_gdecl' (A.TypeDef(aid, tp, ext)) = ()
      | indent_gdecl' (A.FunTypeDef(aid, tp, params, nil, ext)) = ()
      | indent_gdecl' (A.FunTypeDef(aid, tp, params, specs, ext)) =
        (* see A.Function with non-nil specs below *)
          indent_specs specs (col1 ext + min_indent, max_col)
      | indent_gdecl' (A.Function(fun_name, result, params, NONE, nil, is_extern, ext)) =
	(* no pre/postconditions, no body *)
        ()
      | indent_gdecl' (A.Function(fun_name, result, params, NONE, specs, is_extern, ext)) =
          (* col1 ext + min_indent works, because '//@' is 3 characters, >= min_indent *)
          indent_specs specs (col1 ext + min_indent, max_col)
      | indent_gdecl' (A.Function(fun_name, result, params, SOME(s), nil, is_extern, ext)) =
          (* ignore the placement of braces; check seqence of statements
           * constituting the body *)
          indent_seq s (col1 ext + min_indent, max_col) ext
      | indent_gdecl' (A.Function(fun_name, result, params, SOME(s), specs, is_extern, ext)) =
        let val bounds = (col1 ext + min_indent, max_col)
            val () = indent_specs specs bounds
        in
            indent_seq s bounds ext
        end
      | indent_gdecl' (A.Pragma(A.UseLib(libname, _), ext)) = ()
      | indent_gdecl' (A.Pragma(A.UseFile(filename, _), ext)) = ()
      | indent_gdecl' (A.Pragma(A.Raw(pname, pargs), ext)) =
        ( ErrorMsg.warn ext ("unrecognized pragma " ^ pname)
        ; () )

    (* indent_gdecl gdecl = ()
     * Check indentation of global declaration 'gdecl'.
     * Should be at left margin (column 0) *)
    fun indent_gdecl (gdecl) =
        let val ext = gdecl_ext gdecl
            val () = if out_of_bounds (col1 ext) (1, 1)
                     then ErrorMsg.warn ext
                          ("top level declaration indented\n" ^ oob (col1 ext) (1,1))
                     else ()
            val () = indent_gdecl' gdecl
        in
            ()
        end

    (* indent_gdecls gdecls = ()
     * Check indentation of all global declarations 'gdecls' *)
    fun indent_gdecls nil = ()
      | indent_gdecls (gdecl::gdecls) =
        ( indent_gdecl gdecl
        ; indent_gdecls gdecls )

    fun warn_program (gdecls) = indent_gdecls gdecls

end (* structure Warn *)
