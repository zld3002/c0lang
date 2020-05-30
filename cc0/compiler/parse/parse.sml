(* C0 Compiler
 * Parsing
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature PARSE =
sig

  (* parse filename process_library process_file = Ast.program
   * filename - the path to a C0 file that we will parse
   * process_library - function for processing #use <...> pragmas
   * process_file - function for processing #use "..." pragmas
   *)
  val parse: string 
             -> (string -> Ast.gdecl list) 
             -> (string -> string -> Ast.gdecl list) 
             -> Ast.program

  (* Interactive top-level hook *)
  (* parse_stm ft = NONE indicates incomplete parse; must be restarted
   * parse_stm ft = SOME(s,ft') returns statement s and remaining front ft'
   * if ft' = Stream.Cons((Terminal.EOL,_), _) we have an exact parse;
   * otherwise some tokens remain in ft' to be parsed further.
   * Any annotations are already folded into the statement s.
   *)
  val parse_stm : C0Lex.lexresult Stream.front
                  -> (Ast.stm * C0Lex.lexresult Stream.front) option

end

structure Parse :> PARSE =
struct

structure A = Ast
structure PS = ParseState
structure M = Stream
structure T = Terminal
structure L = C0Lex

fun t_toString T.ANNO_BEGIN = "'//@' or '/*@'"
  | t_toString T.ANNO_END = "<end of annotation>"
  | t_toString t = "'" ^ T.toString t ^ "'"

fun ts_toString (nil) = ""
  | ts_toString (t::nil) = " or " ^ t_toString t
  | ts_toString (t::ts) = t_toString t ^ ", " ^ ts_toString ts

fun ^^(s1,s2) = s1 ^ "\n[Hint: " ^ s2 ^ "]"
infix ^^

fun parse_error (region, s) =
    ( ErrorMsg.error (PS.ext region) s
    ; raise ErrorMsg.Error )

fun msg_expected t' t =
    ("expected " ^ t_toString t' ^ ", found: " ^ t_toString t)

fun error_expected (region, t', t) =
    ( ErrorMsg.error (PS.ext region) (msg_expected t' t)
    ; raise ErrorMsg.Error) 

fun error_expected_h (region, t', t, error_hint) =
    ( ErrorMsg.error (PS.ext region) (msg_expected t' t ^^ error_hint)
    ; raise ErrorMsg.Error )

fun msg_expected_list ts t =
    "expected one of " ^ ts_toString ts ^ ", found: " ^ t_toString t

fun error_expected_list (region, ts, t) =
    ( ErrorMsg.error (PS.ext region) (msg_expected_list ts t)
    ; raise ErrorMsg.Error )

fun error_expected_list_h (region, ts, t, error_hint) =
    ( ErrorMsg.error (PS.ext region) (msg_expected_list ts t ^^ error_hint)
    ; raise ErrorMsg.Error )
    
(* EOL is raised for the interactive top-level parser only
 * It indicates an attempt to analyze tokens beyond the current
 * line, which means a top level statement is incomplete.
 * For this to work, the token T.EOL must terminate interactive
 * input, while file input is terminated with T.EOF
 *)
exception EOL

fun location (NONE) = "_"
  | location (SOME(mark)) = Mark.show(mark)
fun mark_exp (e, (left, right)) = A.Marked (Mark.mark' (e, PS.ext (left, right)))
fun mark_stm (A.Assert(exp, nil), (left, right)) =
    let val ext = PS.ext (left, right)
    in
        A.Markeds (Mark.mark' (A.Assert(exp, [A.StringConst(location ext ^ ": assert failed")]),
                               ext))
    end 
  | mark_stm (A.StmDecl(d), r) = A.StmDecl(d) (* do not mark, so we can pattern match! *)
  (* mark sequences, because we no longer pattern match against them? *)
  (* | mark_stm (A.Seq(ds,ss), r) = A.Seq(ds,ss) *) (* do not mark, so we can pattern match! *)
  | mark_stm (s, (left, right)) = A.Markeds (Mark.mark' (s, PS.ext (left, right)))

fun spec_ext spec = case spec of
    A.Requires(_, ext) => ext
  | A.Ensures(_, ext) => ext
  | A.LoopInvariant(_, ext) => ext
  | A.Assertion(_, ext) => ext

type region = int * int

datatype item
  = Tok of T.terminal * region
  | Prefix of int * T.terminal * region * A.oper  (* precedence, operator *)
  | Infix of int * T.terminal * region * A.oper   (* precedence, operator *)
  | Nonfix of T.terminal * region                 (* end of expression marker *)
  | Cast of A.tp * region                         (* cast, works like prefix opr *)
  | Ident of A.ident * region
  | Exp of A.exp * region
  | Exps of A.exp list
  | Simple of A.stm * region
  | Stm of A.stm * region
  | Stms of A.stm list
  | VarDecls of A.vardecl list
  | Tp of A.tp * region
  | GDecl of A.gdecl
  | Fields of A.field list
  | Annos of A.spec list
  | Spec of A.spec
  | Pragma of A.pragma

datatype stack
  = Bot
  | $ of stack * item

infix 2 $

(* debugging only *)
fun itemToString item = case item of
      Tok(t,_) => t_toString t
    | Prefix _ => "Prefix"
    | Infix _ => "Infix"
    | Nonfix _ => "Nonfix"
    | Cast _ => "Cast"
    | Ident(id,_) => "Ident(" ^ Symbol.name id ^ ")"
    | Exp(e,_) => "Exp(_)"
    | Exps(es) => "Exps(_)"
    | Simple(s,_) => "Simple(_)"
    | Stm(s,_) => "Stm(_)"
    | Stms(ss) => "Stms(_)"
    | VarDecls(ds) => "VarDecls(_)"
    | Tp(tp,_) => "Tp(_)"
    | GDecl(gdecl) => "Gdecl(_)"
    | Fields(fs) => "Fields(_)"
    | Annos(specs) => "Annos(_)"
    | Spec(spec) => "Spec(_)"
    | Pragma(p) => "Pragma(_)"

fun stackToString (Bot) = "Bot"
  | stackToString (S $ item) = stackToString S ^ " $ " ^ itemToString item

fun frontToString (M.Cons(t, _)) = t_toString t

fun println (s) = print ("\n" ^ s ^ "\n")
(* end debugging *)

fun update_typetab (A.TypeDef(id, tp, ext)) = Typetab.bind (id, (tp, ext))
  | update_typetab (A.FunTypeDef(id, rtp, params, specs, ext)) =
      Typetab.bind(id, (A.FunType(rtp, params), ext))
  | update_typetab _ = ()

fun is_typename id = case Typetab.lookup id of 
    NONE => false
  | SOME _ => true

fun assign_op t = case t of
    T.PLUSEQ => SOME(A.PLUS)
  | T.MINUSEQ => SOME(A.MINUS)
  | T.STAREQ => SOME(A.TIMES)
  | T.SLASHEQ => SOME(A.DIVIDEDBY)
  | T.PERCENTEQ => SOME(A.MODULO)
  | T.AMPEQ => SOME(A.AND)
  | T.CARETEQ => SOME(A.XOR)
  | T.BAREQ => SOME(A.OR)
  | T.LLEQ => SOME(A.SHIFTLEFT)
  | T.GGEQ => SOME(A.SHIFTRIGHT)
  | T.EQ => NONE (* handled separately *)
  | _ => NONE

fun is_asnop T.EQ = true
  | is_asnop t =
    (case assign_op t
      of NONE => false
       | SOME _ => true)

(* valid occurrences of infix operators are always preceded
 * by an expression which must have already been reduced,
 * valid occurrences of prefix operators never are.
 *)
fun precedes_infix (S $ Exp _) = true
  | precedes_infix _ = false

(* S needed to disambiguate '-' and '*', region r for error message *)
fun opr (S, t, r) = case t of
    T.EXCL =>         Prefix(13, t, r, A.LOGNOT)
  | T.TILDE =>        Prefix(13, t, r, A.COMPLEMENT)
  | T.MINUS => if precedes_infix S
               then   Infix(11, t, r, A.MINUS)
               else   Prefix(13, t, r, A.NEGATIVE)
  | T.STAR => if precedes_infix S
              then    Infix(12, t, r, A.TIMES)
              else    Prefix(13, t, r, A.DEREF)
  (* T.STAR =>        Infix(12, t, r, A.TIMES) see above *)
  | T.SLASH =>        Infix(12, t, r, A.DIVIDEDBY)
  | T.PERCENT =>      Infix(12, t, r, A.MODULO)
  | T.PLUS =>         Infix(11, t, r, A.PLUS)
  (* T.MINUS =>       Infix(11, A.MINUS) see above *)
  | T.LL =>           Infix(10, t, r, A.SHIFTLEFT)
  | T.GG =>           Infix(10, t, r, A.SHIFTRIGHT)
  | T.LESS =>         Infix(9, t, r, A.LESS)
  | T.LEQ =>          Infix(9, t, r, A.LEQ)
  | T.GEQ =>          Infix(9, t, r, A.GEQ)
  | T.GREATER =>      Infix(9, t, r, A.GREATER)
  | T.EQEQ =>         Infix(8, t, r, A.EQ)
  | T.EXCLEQ =>       Infix(8, t, r, A.NOTEQ)
  | T.AMP =>          Infix(7, t, r, A.AND) (* prefix role is handled directly in p_exp *)
  | T.CARET =>        Infix(6, t, r, A.XOR)
  | T.BAR =>          Infix(5, t, r, A.OR)
  | T.AMPAMP =>       Infix(4, t, r, A.LOGAND)
  | T.BARBAR =>       Infix(3, t, r, A.LOGOR)
  | T.QUEST =>        Infix(2, t, r, A.COND) (* opr is unused *)
  | T.COLON =>        Infix(2, t, r, A.COND) (* opr is unused *)
  | _ =>              Nonfix(t, r)

fun is_ternary (T.QUEST) = true
  | is_ternary (T.COLON) = true
  | is_ternary _ = false

fun reduce_ternary (T.COLON, T.COLON) = true (* must reduce here *)
  | reduce_ternary (_, _) = false (* shift all other combinations *)

fun type_start t = case t of
    T.INT => true
  | T.BOOL => true
  | T.STRING => true
  | T.CHAR => true
  | T.VOID => true
  | T.STRUCT => true
  | T.IDENT(s) => is_typename (Symbol.symbol s)
  | _ => false

(* have names been entered when this is called? *)
fun type_name id = case Typetab.lookup id of
    SOME((A.FunType _, _)) => A.FunTypeName(id)
  | SOME((_, _)) => A.TypeName(id)
  (* NONE should be impossible *)

fun var_name (A.Var(vid)) = SOME(Symbol.name vid)
  | var_name (A.Marked(marked_exp)) =
      var_name (Mark.data marked_exp)
  | var_name _ = NONE

val Nop = A.Seq([],[])
val One = Word32.fromInt(1)

(* This is a hand-written shift/reduce parser
 * I have tried to resist the temptation to optimize or transform,
 * since it is very easy to make mistakes.
 *
 * Parsing functions are named p_<nonterminal>, possibly with a suffix
 * for intermediate parsing states.  Reducing functions are named
 * r_<nonterminal>, possibly with a suffix for intermediate states.
 * With few exceptions, a parsing functions have type
 *
 * p_<nonterminal> : stack * L.lexresult M.Front -> stack * L.lexresult M.Front
 * r_<nonterminal> : stack -> stack
 *
 * Note that in input and output of the parsing function, the first
 * token of the lexer stream is exposed (type L.lexresult M.Front) which
 * make for easy matching and composition of these functions.
 *
 * Generally p_<nt> will consume terminals for an <nt> from the lexresult
 * stream and return with the resulting abstract syntax for <nt> onto the stack.
 * Generally r_<nt> will consume a mix of terminal and nonterminals on
 * the stack and push the abstract syntax for an <nt> onto the stack.
 *
 * While parsing expression with infix, prefix, and postfix operators
 * we continue parsing, extending the expression until we encounter
 * a terminal that completes that is not part of an expression.
 *
 * p_<nt> is a function that parses nonterminal <nt>
 * r_<nt> is a function that reduces nonterminal <nt>
 * c_<cond> is a function that checks condition <cond>
 * e_<error> is a function that reports error <error>
 * m_<nt> is a function that marks nonterminal <nt> with region information
 *)

(* Always call 'first ST' to extract the first token for
 * examination.  This will raise the correct exception if
 * interactive input is incomplete. *)
fun first (S, M.Cons((T.EOL, r), ts')) = raise EOL
  | first (S, M.Cons((t, r), ts')) = t

(* This above is a stop-gap.  More elegant would be:
 *
 * fun first (S, M.Cons((T.EOL, r), ts')) = first (S, M.force ts')
 *   | first (S, M.Cons((t, r), ts')) = t
 *
 * but this would require that the interactive lexer construct
 * an appropriate ts' 
 *)

fun shift (S, M.Cons((t, r), ts')) = (S $ Tok(t, r), M.force ts')
fun reduce reduce_fun (S, ft) = (reduce_fun S, ft)

fun drop (S, M.Cons((t, r), ts')) = (S, M.force ts') (* use sparingly *)
fun push item (S, ft) = (S $ item, ft)

fun >>(f,g) = fn x => g(f(x))
fun |>(x,f) = f x

infixr 2 >>
infix 1 |>

(* region manipulation *)
fun join (left1, right1) (left2, right2) = (left1, right2)
fun here (S, M.Cons((t, r), ts')) = r
val nowhere = (0,0)

(* Translating literals *)

fun dec2word32 (s, region) =
    (case Word32Signed.fromString s
      of NONE => parse_error(region, "ill-formed decimal literal '" ^ s ^ "'")
       | SOME(w) => w)
    handle Overflow => parse_error(region, "decimal integer constant '" ^ s ^ "' out of range")

fun hex2word32 (s, region) =
    (case Word32Signed.fromHexString s
      of NONE => parse_error(region, "ill-formed hexadecimal literal '" ^ s ^ "'")
       | SOME(w) => w)
    handle Overflow => parse_error(region, "hexadecimal integer constant '" ^ s ^ "' out of range")

fun str2char (s, region) =
    (case C0Char.fromC0String s
      of NONE => parse_error(region, "ill-formed character literal " ^ s)
       | SOME(c) => c)

(* Declarations are initially parsed as A.StmDecl(d).
 * When we parse a sequence of statements inside a block,
 * we need to resolve the scope of declarations.  In abstract
 * syntax, all sequences have the form A.Seq(ds, ss), where
 * ds is a sequence of declarations and ss is their scope
 *
 * resolve_scope(ss, (ds_rev, scope_rev)) = A.Seq(ds', ss')
 * accumulates the statements in ss into (reverse) declarations
 * ds_rev and (reverse) scope scope_rev, where scope_rev
 * has no declarations.  When encountering a declaration
 * after another kind of statement inside a block, a new
 * scope is opened.
 *)
fun resolve_scope (A.StmDecl(d)::ss, (ds_rev, nil)) =
      (* continuing initial decls *)
      resolve_scope (ss, (d::ds_rev, nil))
  | resolve_scope (A.StmDecl(d)::ss, (ds_rev, scope_rev as (_::_))) =
      (* decl in middle of block, create new scope and append at end *)
      A.Seq(List.rev ds_rev, List.rev (resolve_scope(ss, ([d], nil))::scope_rev))
  (* Sequences may now be terminated by annotations *)
  (* Dec 22, 2012 -fp *)
  (*
  | resolve_scope (A.Anno(specs as (_::_))::nil, (ds_rev, scope_rev)) =
      (* non-empty annotation cannot be last stmt in block, allow? *)
      ( ErrorMsg.error (spec_ext (List.last specs))
                       ("annotation must precede statement" ^^ "use '{}' after annotation if necessary")
      ; raise ErrorMsg.Error )
  *)
  | resolve_scope (s::ss, (ds_rev, scope_rev)) =
      (* s not decl, add to current scope *)
      resolve_scope (ss, (ds_rev, s::scope_rev))
  | resolve_scope (nil, (ds_rev, scope_rev)) =
      A.Seq(List.rev ds_rev, List.rev scope_rev)

(* Parsing functions *)

(* Global declarations *)
(* T.EOL can not arise here, because we only parse statements at the interactive top level *)
fun p_gdecl ST = case first ST of 
    T.STRUCT => ST |> shift >> p_ident >> p_struct_or_fun
  | T.PRAGMA(_) => ST |> p_pragma
  | T.TYPEDEF => ST |> shift >> p_typedef
  | T.EOF => ST
  | t => if type_start t
         then ST |> p_fun
         else ST |> e_gdecl

and e_gdecl ST = case first ST of
    t as T.IDENT(s) => parse_error (here ST, "identifier " ^ t_toString t ^ " at top level "
                                    ^^ "is " ^ s ^ " an undefined type name?")
  | t as T.SEMI => parse_error (here ST, "unexpected token " ^ t_toString t ^ " at top level"
                                ^^ "function definitions should not be terminated by ';'")
  | t => parse_error (here ST, "unexpected token " ^ t_toString t ^ " at top level")

and r_gdecl S = r_gdecl_1 S    (* mlton performance bug work-around *)
and r_gdecl_1 (S $ Tok(T.STRUCT,r1) $ Ident(sid,_) $ Tok(T.SEMI,r2)) =
      S $ GDecl(A.Struct(sid, NONE, false, PS.ext(join r1 r2)))
  | r_gdecl_1 (S $ Tok(T.STRUCT,r1) $ Ident(sid,_)
               $ Tok(T.LBRACE,_) $ Fields(fields) $ Tok(T.RBRACE,_) $ Tok(T.SEMI,r2)) =
      S $ GDecl(A.Struct(sid, SOME(fields), false, PS.ext(join r1 r2)))
  | r_gdecl_1 (S $ Tok(T.TYPEDEF,r1) $ Tp(tp,_) $ Ident(aid,_) $ Tok(T.SEMI,r2)) =
      S $ GDecl(A.TypeDef(aid, tp, PS.ext(join r1 r2)))
  | r_gdecl_1 (S $ Tok(T.TYPEDEF,r1) $ Tp(tp,_) $ Ident(fid,_) $ VarDecls(parmlist) $ Tok(T.SEMI,r2)) =
      S $ GDecl(A.FunTypeDef(fid, tp, parmlist, nil, PS.ext(join r1 r2)))
  | r_gdecl_1 (S $ Tok(T.TYPEDEF,r1) $ Tp(tp,_) $ Ident(fid,_) $ VarDecls(parmlist) $ Annos(specs) $ Tok(T.SEMI,r2)) =
      S $ GDecl(A.FunTypeDef(fid, tp, parmlist, specs, PS.ext(join r1 r2)))
  | r_gdecl_1 (S $ Tok(T.PRAGMA(s),r) $ Pragma(pragma)) =
      S $ GDecl(A.Pragma(pragma, PS.ext(r)))
  | r_gdecl_1 S = r_gdecl_2 S
    (* function declarations must come below function type definitions *)
and r_gdecl_2 (S $ Tp(tp,r1) $ Ident(vid,_) $ VarDecls(parmlist) $ Tok(T.SEMI,r2)) =
       S $ GDecl(A.Function(vid, tp, parmlist, NONE, nil, false, PS.ext(join r1 r2)))
  | r_gdecl_2 (S $ Tp(tp,r1) $ Ident(vid,_) $ VarDecls(parmlist) $ Annos(specs) $ Tok(T.SEMI,r2)) =
       S $ GDecl(A.Function(vid, tp, parmlist, NONE, specs, false, PS.ext(join r1 r2)))
  | r_gdecl_2 (S $ Tp(tp,r1) $ Ident(vid,_) $ VarDecls(parmlist) $ Stm(stm,r2)) =
       S $ GDecl(A.Function(vid, tp, parmlist, SOME(stm), nil, false, PS.ext(join r1 r2)))
  | r_gdecl_2 (S $ Tp(tp,r1) $ Ident(vid,_) $ VarDecls(parmlist) $ Annos(specs) $ Stm(stm,r2)) =
       S $ GDecl(A.Function(vid, tp, parmlist, SOME(stm), specs, false, PS.ext(join r1 r2)))


(* Pragmas *)
(* first ST = '#<pragma> line' *)
and p_pragma ST = case first ST of
    T.PRAGMA(line) => (* call external parser *)
    let val pragma = ParsePragma.parse_pragma line NONE
    (* in ST |> drop >> push (GDecl(A.Pragma(pragma, NONE))) end *)
    (* use line below instead to obtain correct region for pragma *)
    (* December 22, 2012 -fp *)
    in ST |> shift >> push (Pragma(pragma)) >> reduce r_gdecl end

(* Type definitions *)
(* S = _ $ 'typedef' *)
and p_typedef ST = ST |> p_tp >> p_ident >> p_typedef1
and p_typedef1 ST = case first ST of
    T.SEMI => ST |> shift >> reduce r_gdecl (* ordinary type definition *)
  | T.LPAREN => (* function type definition *)
      ST |> p_parmlist >> p_anno_opt
  | t => error_expected_list (here ST, [T.SEMI, T.LPAREN], t)
  (* improve error message? *)
  (*
  | t => parse_error (here ST, "terminate type definition with ';'"
                                   ^^ "found " ^ t_toString t)
  *)

and p_anno_opt ST = case first ST of
    T.SEMI => ST |> shift >> reduce r_gdecl
  | T.ANNO_BEGIN => ST |> push (Annos []) >> p_annos >> p_anno_opt
  | t => error_expected_list (here ST, [T.SEMI, T.ANNO_BEGIN], t)

(* Struct or function disambiguation *)
(* S = _ $ 'struct' $ <sid> *)
and p_struct_or_fun ST = case first ST of
    T.SEMI => ST |> shift >> reduce r_gdecl  (* struct decl *)
  | T.LBRACE => ST |> shift >> push (Fields []) >> p_struct_body  (* struct defn *)
  | _ => (* have shifted 'struct s', reduce it, then continue with type *)
    ST |> reduce r_tp >> p_fun1 (* function decl or defn *)

(* Structs *)
and p_struct_body ST = case first ST of
    T.RBRACE => ST |> shift >> p_terminal_h T.SEMI "terminate preceding struct definition with ';'"
                   >> reduce r_gdecl
  | _ => ST |> p_tp >> p_ident >> p_terminal_h T.SEMI "terminate all struct fields with ';'"
            >> reduce r_fields >> p_struct_body

and r_fields (S $ Fields(fs) $ Tp(tp,r1) $ Ident(fid,_) $ Tok(T.SEMI,r2)) =
      S $ Fields(fs @ [A.Field(fid, tp, PS.ext(join r1 r2))])

(* Annotations *)
(* return S $ Annos(specs) or just S *)
and p_annos ST = case first ST of
    T.ANNO_BEGIN => ST |> shift >> push (Annos []) >> p_anno >> reduce r_annos >> p_annos
  | _ => ST

and r_annos (S $ Annos(specs1) $ Annos(specs2)) = S $ Annos(specs1 @ specs2)

and p_anno ST = case first ST of
    T.ANNO_END => ST |> shift >> reduce r_anno
  | T.REQUIRES => ST |> shift >> p_specs
  | T.ENSURES => ST |> shift >> p_specs
  | T.LOOP_INVARIANT => ST |> shift >> p_specs
  | T.ASSERT => ST |> shift >> p_specs
  | t => error_expected_list (here ST, [T.REQUIRES, T.ENSURES, T.LOOP_INVARIANT, T.ASSERT], t)

and r_anno (S $ Tok(T.ANNO_BEGIN,_) $ Annos(specs) $ Tok(T.ANNO_END,_)) =
      S $ Annos(specs)

(* S = _ $ 'requires' | 'ensures' | 'loop_invariant' | 'assert' *)
and p_specs ST = ST |> p_exp >> p_terminal_h T.SEMI "terminate annotations with ';'"
                    >> reduce r_spec >> p_anno

and r_spec (S $ Annos(specs) $ Tok(T.REQUIRES,r1) $ Exp(e,_) $ Tok(T.SEMI,r2)) =
      S $ Annos(specs @ [A.Requires(e, PS.ext(join r1 r2))])
  | r_spec (S $ Annos(specs) $ Tok(T.ENSURES,r1) $ Exp(e,_) $ Tok(T.SEMI,r2)) =
      S $ Annos(specs @ [A.Ensures(e, PS.ext(join r1 r2))])
  | r_spec (S $ Annos(specs) $ Tok(T.LOOP_INVARIANT,r1) $ Exp(e,_) $ Tok(T.SEMI,r2)) =
      S $ Annos(specs @ [A.LoopInvariant(e, PS.ext(join r1 r2))])
  | r_spec (S $ Annos(specs) $ Tok(T.ASSERT,r1) $ Exp(e,_) $ Tok(T.SEMI,r2)) =
      S $ Annos(specs @ [A.Assertion(e, PS.ext(join r1 r2))])

(* Functions *)
and p_fun ST = ST |> p_tp >> p_fun2
and p_fun1 ST = (* already parsed 'struct s', continue with type *)
      ST |> p_tp1 >> p_fun2
and p_fun2 ST = (* type already parsed *)
      ST |> p_ident >> p_parmlist >> p_fun_decl_or_defn
and p_fun_decl_or_defn ST = case first ST of
    T.SEMI => (* fun decl *) ST |> shift >> reduce r_gdecl
  | T.LBRACE => (* fun defn *) ST |> p_stmt_block >> reduce r_gdecl
  | T.ANNO_BEGIN => ST |> push (Annos []) >> p_annos >> p_fun_decl_or_defn
  | t => error_expected_list (here ST, [T.SEMI, T.LBRACE, T.ANNO_BEGIN], t)

and p_parmlist ST = case first ST of
    T.LPAREN => ST |> shift >> push (VarDecls []) >> p_parmlist0
  | t as T.SEMI => error_expected_h (here ST, T.LPAREN, t, "no global variable declarations permitted")
  | t => error_expected (here ST, T.LPAREN, t)
and p_parmlist0 ST = case first ST of
    T.RPAREN => ST |> shift >> reduce r_parmlist
  | _ => ST |> p_parmlist1
and p_parmlist1 ST = ST |> p_tp >> p_ident >> reduce r_parmlist1 >> p_parmlist2
and p_parmlist2 ST = case first ST of
    T.RPAREN => ST |> shift >> reduce r_parmlist
  | T.COMMA => ST |> drop >> p_parmlist1 (* drop comma, no shift *)
  | t => error_expected_list (here ST, [T.RPAREN, T.COMMA], t)

and r_parmlist1 (S $ VarDecls(parmlist) $ Tp(tp,r1) $ Ident(vid,r2)) =
      S $ VarDecls(parmlist @ [A.VarDecl(vid, tp, NONE, PS.ext(join r1 r2))])
and r_parmlist (S $ Tok(T.LPAREN,_) $ VarDecls(parmlist) $ Tok(T.RPAREN,_)) = S $ VarDecls(parmlist)

(* Statements *)
and p_stmt ST = case first ST of
    T.IF => ST |> shift >> p_paren_exp >> p_stmt >> p_stmt_if_then
  | T.WHILE => ST |> shift >> p_paren_exp >> p_loopbody >> reduce r_stmt
  | T.FOR => ST |> shift >> p_terminal T.LPAREN
                >> p_simple_opt >> p_terminal T.SEMI
                >> p_exp >> p_terminal T.SEMI
                >> p_simple_opt >> p_terminal T.RPAREN
                >> p_loopbody >> reduce r_stmt
  | T.CONTINUE => ST |> shift >> p_terminal T.SEMI >> reduce r_stmt
  | T.BREAK => ST |> shift >> p_terminal T.SEMI >> reduce r_stmt
  | T.RETURN => ST |> shift >> p_stmt_return
  | T.LBRACE => ST |> p_stmt_block (* don't shift *)
  | T.ASSERT => ST |> shift >> p_terminal T.LPAREN >> p_exp >> p_terminal T.RPAREN >> p_terminal T.SEMI
                   >> reduce r_stmt
  | T.ERROR => ST |> shift >> p_terminal T.LPAREN >> p_exp >> p_terminal T.RPAREN >> p_terminal T.SEMI
                   >> reduce r_stmt
  | T.ANNO_BEGIN => ST |> push (Annos []) (* do not shift! *)
                       >> p_annos >> p_stmt >> reduce r_stmt
  | _ => ST |> p_simple >> p_terminal T.SEMI >> reduce r_stmt

and p_simple_opt ST = case first ST of
    T.SEMI => ST |> push (Simple(Nop, here ST))
  | T.RPAREN => ST |> push (Simple(Nop, here ST))
  | _ => ST |> p_simple
and p_simple ST =
    if type_start (first ST)
    then ST |> p_decl
    else ST |> p_assign

and p_decl ST = ST |> p_tp >> p_ident >> p_decl_init_opt
and p_decl_init_opt ST = case first ST of
    T.EQ => ST |> shift >> p_exp >> reduce r_decl_or_assign
  | _ => ST |> reduce r_decl_or_assign

and p_assign ST = ST |> p_exp >> p_assign1
and p_assign1 ST = case first ST of
    T.PLUSPLUS => ST |> shift >> reduce r_decl_or_assign
  | T.MINUSMINUS => ST |> shift >> reduce r_decl_or_assign
  | t => if is_asnop t
         then ST |> shift >> p_exp >> reduce r_decl_or_assign
         else (* exp as stmt, already on stack *)
             ST |> reduce r_simple_exp

and p_stmt_block ST =
    ST |> p_terminal T.LBRACE >> push (Stms []) >> p_stmtlist
       >> p_terminal T.RBRACE >> reduce r_stmt
    (* no other possibilities *)
and p_stmtlist ST = case first ST of
    T.RBRACE => ST (* end of statement lists; do not shift *)
  | _ => ST |> p_annos_or_stmt >> reduce r_stmtlist >> p_stmtlist

(* annotations must be handled specially in statement lists
 * so that they can precede declarations without limiting
 * their scope *)
and p_annos_or_stmt TS = case first TS of
    T.ANNO_BEGIN => TS |> push (Annos []) >> p_annos (* don't shift *)
  | _ => TS |> p_stmt

(* reduce to get innermost association for 'else' *)
and p_stmt_if_then TS = case first TS of
    T.ELSE => TS |> shift >> p_stmt >> reduce r_stmt
  | _ => TS |> reduce r_stmt

and p_stmt_return ST = case first ST of
    T.SEMI => ST |> shift >> reduce r_stmt
  | _ => ST |> p_exp >> p_terminal T.SEMI >> reduce r_stmt

and p_loopbody ST = ST |> push (Annos []) >> p_annos >> p_stmt

and m_stm(s,r) = Stm(mark_stm(s,r), r)
and m_simple(s,r) = Simple(mark_stm(s,r), r)

and r_stmt S = r_stmt_1 S     (* mlton performance bug work-around *)
and r_stmt_1 (S $ Tok(T.IF,r1) $ Tok(T.LPAREN,_) $ Exp(e,_) $ Tok(T.RPAREN,_) $ Stm(s1,_)
              $ Tok(T.ELSE,_) $ Stm(s2,r2)) =
      S $ m_stm(A.If(e, s1, s2),join r1 r2)
  | r_stmt_1 (S $ Tok(T.IF,r1) $ Tok(T.LPAREN,_) $ Exp(e,_) $ Tok(T.RPAREN,_) $ Stm(s1,r2)) =
      S $ m_stm(A.If(e, s1, Nop),join r1 r2)
  | r_stmt_1 (S $ Tok(T.WHILE,r1) $ Tok(T.LPAREN,_) $ Exp(e,_) $ Tok(T.RPAREN,_)
              $ Annos(invs) $ Stm(s,r2)) =
      S $ m_stm(A.While(e, invs, s),join r1 r2)
  | r_stmt_1 (S $ Tok(T.FOR,r1) $ Tok(T.LPAREN,_) $ Simple(s1,_) $ Tok(T.SEMI,_)
              $ Exp(e2,_) $ Tok(T.SEMI,_) $ Simple(s3,_) $ Tok(T.RPAREN,_)
              $ Annos(invs) $ Stm(s4,r2)) =
      S $ m_stm(A.For(s1, e2, s3, invs, s4),join r1 r2)
  | r_stmt_1 S = r_stmt_2 S
and r_stmt_2 (S $ Tok(T.CONTINUE,r1) $ Tok(T.SEMI,r2)) = S $ m_stm(A.Continue,join r1 r2)
  | r_stmt_2 (S $ Tok(T.BREAK,r1) $ Tok(T.SEMI,r2)) = S $ m_stm(A.Break,join r1 r2)
  | r_stmt_2 (S $ Tok(T.RETURN,r1) $ Tok(T.SEMI,r2)) = S $ m_stm(A.Return(NONE),join r1 r2)
  | r_stmt_2 (S $ Tok(T.RETURN,r1) $ Exp(e,_) $ Tok(T.SEMI,r2)) = S $ m_stm(A.Return(SOME(e)),join r1 r2)
  | r_stmt_2 (S $ Tok(T.LBRACE,r1) $ Stms(slist) $ Tok(T.RBRACE,r2)) =
      S $ m_stm(resolve_scope(slist, ([],[])),join r1 r2)
  | r_stmt_2 S = r_stmt_3 S
and r_stmt_3 (S $ Tok(T.ASSERT,r1) $ Tok(T.LPAREN,_) $ Exp(e,_) $ Tok(T.RPAREN,_) $ Tok(T.SEMI,r2)) =
      S $ m_stm(A.Assert(e, nil),join r1 r2)
  | r_stmt_3 (S $ Tok(T.ERROR,r1) $ Tok(T.LPAREN,_) $ Exp(e,_) $ Tok(T.RPAREN,_) $ Tok(T.SEMI,r2)) =
      S $ m_stm(A.Error e,join r1 r2)
  | r_stmt_3 (S $ Annos(specs) $ Stm(s,r)) =
      (* do not mark the artifical sequence below; it does not have a
       * proper source region. -fp Aug 23, 2013 *)
      S $ Stm(A.Seq([], [A.Anno(specs), s]),r) (* needs to become one stmt *)
  | r_stmt_3 (S $ Simple(s,r1) $ Tok(T.SEMI,r2)) = S $ m_stm(s,join r1 r2)
  (* the above should be exhaustive *)
  (* r_stmt_3 S = ( println (stackToString S) ; raise Domain ) *)

and r_decl_or_assign (S $ Tp(tp,r1) $ Ident(vid,r2)) =
      S $ Simple(A.StmDecl(A.VarDecl(vid, tp, NONE, PS.ext(join r1 r2))), join r1 r2)
  | r_decl_or_assign (S $ Tp(tp,r1) $ Ident(vid,_) $ Tok(T.EQ,_) $ Exp(e,r2)) =
      S $ Simple(A.StmDecl(A.VarDecl(vid, tp, SOME(e), PS.ext(join r1 r2))), join r1 r2)
  | r_decl_or_assign (S $ Exp(e1,r1) $ Tok(t,_) $ Exp(e2,r2)) =
      (* t must be assignment operator *)
      S $ m_simple(A.Assign(assign_op t, e1, e2), join r1 r2)
  | r_decl_or_assign (S $ Exp(e,r1) $ Tok(T.PLUSPLUS,r2)) =
      S $ m_simple(A.Assign(SOME(A.PLUS), e, A.IntConst(One)), join r1 r2) (* mark_exp(e,r1) ? *)
  | r_decl_or_assign (S $ Exp(e,r1) $ Tok(T.MINUSMINUS,r2)) =
      S $ m_simple(A.Assign(SOME(A.MINUS), e, A.IntConst(One)), join r1 r2) (* mark_exp(e,r1) ? *)
  (* the above should be exhaustive *)
  (* | r_decl_or_assign S = ( println (stackToString S) ; raise Domain ) *)

and r_simple_exp (S $ Exp(e,r)) = S $ Simple(mark_stm(A.Exp(e),r),r)

(* the sequence normal form is ugly *)
and r_stmtlist (S $ Stms(ss) $ Stm(s,_)) = S $ Stms(ss @ [s])
  | r_stmtlist (S $ Stms(ss) $ Annos(specs)) = S $ Stms(ss @ [A.Anno(specs)])

(* Types *)
and p_tp ST = case first ST of
    T.INT => ST |> shift >> reduce r_tp >> p_tp1
  | T.BOOL => ST |> shift >> reduce r_tp >> p_tp1
  | T.STRING => ST |> shift >> reduce r_tp >> p_tp1
  | T.CHAR => ST |> shift >> reduce r_tp >> p_tp1
  | T.VOID => ST |> shift >> reduce r_tp >> p_tp1
  | T.STRUCT => ST |> shift >> p_ident >> reduce r_tp >> p_tp1
  | T.IDENT(s) =>
    let val id = Symbol.symbol(s)
    in if is_typename (Symbol.symbol s)
       (* only shift valid type names, signal error otherwise *)
       then ST |> shift >> reduce r_tp >> p_tp1
       else parse_error (here ST, "expected a type, found identifier " ^ t_toString (T.IDENT(s)))
    end
  | t => parse_error (here ST, "expected a type, found " ^ t_toString(t))

(* prefix of a type already parsed and on stack, possibly the whole type *)
and p_tp1 ST = case first ST of (* postfix operators; always shift and reduce *)
    T.STAR => ST |> shift >> reduce r_tp >> p_tp1
  | T.LBRACKET => ST |> shift >> p_terminal_h T.RBRACKET "array length cannot be specified in type; use '[]'?"
                     >> reduce r_tp >> p_tp1
  | _ => ST (* no postifx operator: return since already reduced *)

and r_tp (S $ Tok(T.INT,r)) = S $ Tp(A.Int,r)
  | r_tp (S $ Tok(T.BOOL,r)) = S $ Tp(A.Bool,r)
  | r_tp (S $ Tok(T.STRING,r)) = S $ Tp(A.String,r)
  | r_tp (S $ Tok(T.CHAR,r)) = S $ Tp(A.Char,r)
  | r_tp (S $ Tok(T.VOID,r)) = S $ Tp(A.Void,r)
  | r_tp (S $ Tok(T.STRUCT,r1) $ Ident(sid,r2)) = S $ Tp(A.StructName(sid),join r1 r2)
  | r_tp (S $ Tok(T.IDENT(s),r)) = S $ Tp(type_name(Symbol.symbol s),r) (* s is valid type name if on stack *)
  | r_tp (S $ Tp(tp,r1) $ Tok(T.STAR,r2)) = S $ Tp(A.Pointer(tp),join r1 r2)
  | r_tp (S $ Tp(tp,r1) $ Tok(T.LBRACKET,_) $ Tok(T.RBRACKET,r2)) = S $ Tp(A.Array(tp),join r1 r2)
  (* above should be exhaustive *)

(***************)
(* Expressions *)
(***************)

and m_exp (e, r) = Exp(mark_exp(e,r),r)

(* do not reduce to expression, because p_paren_exp is
 * used for 'if' and 'while', to be reduced with statement *)
and p_paren_exp ST =
    ST |> p_terminal T.LPAREN >> p_exp >> p_terminal T.RPAREN

(* needed for casts which may start an expression *)
and p_paren_exp_or_tp ST =
    ST |> p_terminal T.LPAREN >> p_exp_or_tp

and p_exp_or_tp ST =
    if type_start (first ST)
    then ST |> p_tp >> p_terminal T.RPAREN
    else ST |> p_exp >> p_terminal T.RPAREN

(* check that stack does *not* end in expression *)
and c_follows_nonexp (ST as (S,_)) = case (S, first ST) of
    (S $ Stms _ $ Exp(e,r), T.IDENT(s)) =>
    (case var_name e
      of SOME(id) => parse_error (join r (here ST), "consecutive expressions"
                                  ^^ "undeclared type name '" ^ id ^ "'?")
       | NONE => e_follows_nonexp r ST)
  | (Bot $ Exp(e,r), T.IDENT(s)) =>
    (* when called from coin, where stms are at top level *)
    (case var_name e
      of SOME(id) => parse_error (join r (here ST), "consecutive expressions"
                                  ^^ "undeclared type name '" ^ id ^ "'?")
       | NONE => e_follows_nonexp r ST)
  | (S $ Exp(e,r), _) => e_follows_nonexp r ST
  | (S, t) => ST

and e_follows_nonexp r ST =
    parse_error (join r (here ST), "consecutive expressions"
                 ^^ "missing infix operator?")

(* check that stack *does* end in expression *)
and c_follows_exp msg (ST as ((S $ Exp _), _)) = ST
  | c_follows_exp msg ST =
      parse_error (here ST, msg ^ " operator " ^ t_toString (first ST)
                            ^ " not preceeded by expression")

and follows_exp (ST as (_ $ Exp(e,r), _)) = true
  | follows_exp _ = false

(* parse the maximal initial segment of ft as an expression e
 * returning (S $ Exp(e), ft') *)
and p_exp (ST as (S, ft)) = case (S, first ST) of
    (_, T.LPAREN) => if follows_exp ST
                     then (* possibly invoking function pointer *)
                         p_exp_var_or_call ST
                     else ST |> c_follows_nonexp >> p_paren_exp_or_tp >> reduce r_exp >> p_exp

  (* for literal expressions, shift and reduce, after checking juxtaposition *)
  | (_, T.DECNUM(s)) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp
  | (_, T.HEXNUM(s)) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp
  | (_, T.STRLIT(s)) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp
  | (_, T.CHRLIT(s)) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp
  | (_, T.TRUE) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp
  | (_, T.FALSE) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp
  | (_, T.NULL) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp

  | (_, T.IDENT(s)) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp_var_or_call
  | (_, T.BS_RESULT) => ST |> c_follows_nonexp >> shift >> reduce r_exp >> p_exp

  (* pseudo function calls *)
  | (_, T.BS_LENGTH) => ST |> c_follows_nonexp >> shift >> p_terminal T.LPAREN >> p_exp >> p_terminal T.RPAREN
                           >> reduce r_exp >> p_exp

  (* postfix operators, highest precedence *)
  | (_, T.DOT) => ST |> c_follows_exp "field selection"
                     >> shift >> p_ident >> reduce r_exp >> p_exp
  | (_, T.ARROW) => ST |> c_follows_exp "field dereference"
                       >> shift >> p_ident >> reduce r_exp >> p_exp
  | (_, T.LBRACKET) => ST |> c_follows_exp "array indexing" 
                          >> shift >> p_exp >> p_terminal T.RBRACKET >> reduce r_exp >> p_exp

  (* pseudo function calls involving types *)
  | (_, T.ALLOC) => ST |> c_follows_nonexp >> shift >> p_terminal T.LPAREN >> p_tp >> p_terminal T.RPAREN
                       >> reduce r_exp >> p_exp
  | (_, T.ALLOC_ARRAY) => ST |> c_follows_nonexp >> shift >> p_terminal T.LPAREN >> p_tp >> p_terminal T.COMMA
                             >> p_exp >> p_terminal T.RPAREN >> reduce r_exp >> p_exp
  | (_, T.BS_HASTAG) => ST |> c_follows_nonexp >> shift >> p_terminal T.LPAREN >> p_tp >> p_terminal T.COMMA
                           >> p_exp >> p_terminal T.RPAREN >> reduce r_exp >> p_exp

  (* special case for '&' as a prefix operator, because in C1
   * it can only be applied to function names *)
  | (S, t as T.AMP) => if follows_exp ST
                       then (* infix operator '&' (bitwise and) *)
                           ST |> drop >> p_exp_prec (opr (S, t, here ST))
                       else (* prefix operator '&' (address of) *)
                           ST |> shift >> p_fun_ident >> reduce r_exp >> p_exp
  (* end of expression *)
  | (S, t) => (case opr (S, t, here ST)
                of Nonfix(t', r) => (* nonfix: do not consume token *)
                     ST |> p_exp_prec (Nonfix(t', r))
                 | subject => (* infix or prefix: oper consumes token, use oper.prec. *)
                     ST |> drop >> p_exp_prec subject)

(* operator precedence parsing *)
(* p_exp_prec subject (S, ft) compares precedence of subject to ft
 * to decide if to shift, reduce, or raise an error.
 * Continue if expression could be extended by further tokens. *)
and p_exp_prec subject (ST as (S, ft)) = case (S, subject) of
  (* looking at Exp; possible? *)
    (S, Exp _) => ST |> push subject >> p_exp  (* shift *)

  (* looking at Infix *)
  | (S $ Exp _ $ Infix(k1, t1, _, _) $ Exp _, Infix(k2, t2, _, _)) =>
    (* all infix operators except '?' and ':' are left-associative *)
    if k1 > k2 orelse (k1 = k2 andalso (not (is_ternary t2) orelse reduce_ternary (t1, t2)))
    then ST |> reduce r_exp >> p_exp_prec subject  (* reduce *)
    else ST |> push subject >> p_exp               (* shift *)
  | (S $ Prefix(k1, _, _, _) $ Exp _, Infix (k2, _, _, _)) =>
    (* reduce, since always k1 > k2 in C and C0 *)
      ST |> reduce r_exp >> p_exp_prec subject     (* reduce *)
  | (S $ Cast _ $ Exp _, Infix _) =>
    (* reduce, since precedence of cast > precedence of infix ops in C and C0 *)
      ST |> reduce r_exp >> p_exp_prec subject
  | (S $ Exp _, Infix _) =>  (* preceding two cases don't match *)
      ST |> push subject >> p_exp                  (* shift *)
  (* error conditions for Infix *)
  | (S $ Infix(_, t1, r1, _), Infix(_, t2, r2, _)) =>
      parse_error (join r1 r2, "consecutive infix operators " ^ t_toString t1 ^ " " ^ t_toString t2)
  | (S $ Prefix(_, t1, r1, _), Infix(_, t2, r2, _)) =>
      parse_error (join r1 r2, "prefix operator " ^ t_toString t1 ^ " followed by infix operator " ^ t_toString t2)
  | (S $ Cast(_, r1), Infix(_, t2, r2, _)) =>
      parse_error (join r1 r2, "cast directly followed by infix operator " ^ t_toString t2)
  | (S, Infix(_, t, r, _)) =>
      parse_error (r, "leading infix operator " ^ t_toString t)

  (* looking at Prefix *)
  | (S $ Exp _, Prefix(_, t, r, _)) =>
      parse_error (r, "prefix operator " ^ t_toString t ^ " immediately following expression")
  | (S $ Exp _, Cast(_, r)) =>
      parse_error (r, "cast immediately following expression")
  | (S, Prefix _) => (* always shift, since prefix have higher precedence than infix *)
      ST |> push subject >> p_exp
  | (S, Cast _) => (* always shift, since cast has higher precedence than infix *)
      ST |> push subject >> p_exp

  (* looking at Nonfix, end of expression *)
  (* special cases, due to high precedence of ++ and -- in C
   * which are not operators in C0 *)
  | (S $ Prefix(_, T.STAR, r1, _) $ Exp _, Nonfix(T.PLUSPLUS, r2)) =>
      parse_error (join r1 r2, "for compatibility with C, please write (*e)++ instead of *e++")
  | (S $ Prefix(_, T.STAR, r1, _) $ Exp _, Nonfix(T.MINUSMINUS, r2)) =>
      parse_error (join r1 r2, "for compatibility with C, please write (*e)-- instead of *e--")

  (* at end of expressiong we keep reducing *)
  | (S $ Exp _ $ Infix _ $ Exp _, Nonfix _) => ST |> reduce r_exp >> p_exp_prec subject
  | (S $ Prefix _ $ Exp _, Nonfix _) => ST |> reduce r_exp >> p_exp_prec subject
  | (S $ Cast _ $ Exp _, Nonfix _) => ST |> reduce r_exp >> p_exp_prec subject
  | (S $ Infix(_, t, r, _), Nonfix _) => parse_error (r, "trailing infix operator " ^ t_toString t)
  | (S $ Prefix(_, t, r, _), Nonfix _) => parse_error (r, "trailing prefix operator " ^ t_toString t)
  | (S $ Cast(_, r), Nonfix _) => parse_error(r, "trailing cast")
  | (S $ Exp _, Nonfix _) => ST (* must be reduced if it doesn't match above *)

  (* try to diagnose *)
  | (S, Nonfix _) => e_exp_empty ST (* error: empty expression; see below *)

and e_exp_empty (ST as (S,_)) = case (S, first ST) of
    (S $ Stms _ $ Exp(e,r1) $ Tok(T.LBRACKET,r2), T.RBRACKET) =>
    (case var_name e
      of SOME(id) => parse_error (join r2 (here ST), "empty index expression"
                                  ^^ "undeclared type name '" ^ id ^ "'?")
       | NONE => parse_error (join r2 (here ST), "empty index expression"))
  | (S $ Stms _, T.SEMI) =>
    parse_error (here ST, "extraneous semicolon ';' following statement"
                 ^^ "conditionals, loops, and blocks are not terminated by ';'")
  | (S $ Stms _, t) => parse_error (here ST, "expected statement, found " ^ t_toString t)
  | (S, t) => parse_error (here ST, "expected expression, found " ^ t_toString t)

(* S = _ $ Ident _ or S = _ $ Exp _ if first ST = T.LPAREN *)
and p_exp_var_or_call ST = case first ST of
    T.LPAREN => ST |> shift >> push (Exps []) >> p_explist
                   >> p_terminal T.RPAREN >> reduce r_exp >> p_exp
  | _ => (* not a call; identifier must be a variable (already shifted) *)
    ST |> reduce r_exp >> p_exp

(* S = _ $ Exps _ *)
and p_explist ST = case first ST of
    T.RPAREN => ST (* end of expression list; do not shift *)
  | _ => ST |> p_explist1
and p_explist1 ST = ST |> p_exp >> reduce r_explist >> p_explist2
and p_explist2 ST = case first ST of
    T.COMMA => ST |> drop >> p_explist1
  | T.RPAREN => ST (* end of expression list; do not shift *)
  | t => error_expected_list (here ST, [T.COMMA, T.RPAREN], t)

and r_explist (S $ Exps(es) $ Exp(e,_)) = S $ Exps(es @ [e])

(* reducing expressions *)
and r_exp S = r_exp_1 S        (* mlton performance bug work-around *)

(* literal constants *)
and r_exp_1 (S $ Tok(T.DECNUM(s),r)) = S $ m_exp (A.IntConst(dec2word32(s,r)), r)
  | r_exp_1 (S $ Tok(T.HEXNUM(s),r)) = S $ m_exp(A.IntConst(hex2word32(s,r)),r)
  | r_exp_1 (S $ Tok(T.STRLIT(s),r)) = S $ m_exp(A.StringConst(s),r)
  | r_exp_1 (S $ Tok(T.CHRLIT(s),r)) = S $ m_exp(A.CharConst(str2char(s,r)),r)
  | r_exp_1 (S $ Tok(T.TRUE,r)) = S $ m_exp(A.True,r)
  | r_exp_1 (S $ Tok(T.FALSE,r)) = S $ m_exp(A.False,r)
  | r_exp_1 (S $ Tok(T.NULL,r)) = S $ m_exp(A.Null,r)
  | r_exp_1 (S $ Tok(T.IDENT(s),r)) = S $ Ident(Symbol.symbol s, r)
  | r_exp_1 (S $ Tok(T.BS_RESULT,r)) = S $ m_exp(A.Result, r)
  | r_exp_1 S = r_exp_2 S

(* function calls and pseudo-function calls *)
and r_exp_2 (S $ Tok(T.ALLOC,r1) $ Tok(T.LPAREN,_) $ Tp(tp,_) $ Tok(T.RPAREN,r2)) =
      S $ m_exp(A.Alloc(tp),join r1 r2)
  | r_exp_2 (S $ Tok(T.ALLOC_ARRAY,r1) $ Tok(T.LPAREN,_) $ Tp(tp,_) $ Tok(T.COMMA,_) $ Exp(e,_) $ Tok(T.RPAREN,r2)) =
      S $ m_exp(A.AllocArray(tp, e),join r1 r2)
  | r_exp_2 (S $ Tok(T.BS_LENGTH,r1) $ Tok(T.LPAREN,_) $ Exp(e,_) $ Tok(T.RPAREN,r2)) =
      S $ m_exp(A.Length(e),join r1 r2)
  | r_exp_2 (S $ Tok(T.BS_HASTAG,r1) $ Tok(T.LPAREN,_) $ Tp(tp,_) $ Tok(T.COMMA,_) $ Exp(e,_) $ Tok(T.RPAREN,r2)) =
      S $ m_exp(A.Hastag(tp, e),join r1 r2)
  | r_exp_2 (S $ Ident(vid,r1) $ Tok(T.LPAREN,_) $ Exps(es) $ Tok(T.RPAREN,r2)) =
      S $ m_exp(A.FunCall(vid, es),join r1 r2)
  | r_exp_2 (S $ Exp(e,r1) $ Tok(T.LPAREN,_) $ Exps(es) $ Tok(T.RPAREN,r2)) =
      S $ m_exp(A.Invoke(e, es),join r1 r2)
  | r_exp_2 S = r_exp_3 S

(* field access *)
and r_exp_3 (S $ Exp(e,r1) $ Tok(T.DOT,_) $ Ident(fid,r2)) =
      S $ m_exp(A.Select(e, fid),join r1 r2)
  | r_exp_3 (S $ Exp(e,r1) $ Tok(T.ARROW,_) $ Ident(fid,r2)) =
      S $ m_exp(A.Select(A.OpExp(A.DEREF, [e]), fid), join r1 r2)

  (* address-of, must come before identifiers *)
  | r_exp_3 (S $ Tok(T.AMP,r1) $ Ident(gid,r2)) =
      S $ m_exp(A.AddrOf(gid), join r1 r2)

  (* identifiers, must come after field access and address-of *)
  | r_exp_3 (S $ Ident(vid,r)) = S $ m_exp(A.Var(vid), r)

  (* array access *)
  | r_exp_3 (S $ Exp(e1,r1) $ Tok(T.LBRACKET,_) $ Exp(e2,_) $ Tok(T.RBRACKET,r2)) =
      S $ m_exp(A.OpExp(A.SUB, [e1,e2]), join r1 r2)

  | r_exp_3 S = r_exp_4 S

(* operator precedence *)
and r_exp_4 (S $ Tok(LPAREN,r1) $ Exp(e,_) $ Tok(RPAREN,r2)) = S $ m_exp(e,join r1 r2)
  | r_exp_4 (S $ Tok(LPAREN,r1) $ Tp(tp,_) $ Tok(RPAREN,r2)) = S $ Cast(tp,join r1 r2)
  | r_exp_4 (S $ Exp(e1,r1) $ Infix(_, T.QUEST, _, _) $ Exp(e2,_) $ Infix(_, T.COLON, _, _) $ Exp(e3,r2)) =
      S $ m_exp(A.OpExp (A.COND, [e1, e2, e3]), join r1 r2)

  (* move the next two cases to the p_exp_prec function? *)
  | r_exp_4 (S $ Exp(e1,r1) $ Infix(_, T.QUEST, _, _) $ Exp(e2,r2)) =
      parse_error (join r1 r2, "Conditional 'e1 ? e2 : e3' without else-clause ': e3'")
  | r_exp_4 (S $ Exp(e1,r1) $ Infix(_, T.COLON, _, _) $ Exp(e3,r2)) =
      parse_error (join r1 r2, "Conditional 'e1 ? e2 : e3' without then-clause '? e2'")

  | r_exp_4 (S $ Exp(e1,r1) $ Infix(_, t2, _, o2) $ Exp(e2,r2)) = S $ m_exp(A.OpExp(o2, [e1,e2]), join r1 r2)
  | r_exp_4 (S $ Prefix(_, t1, r1, o1) $ Exp(e1,r2)) = S $ m_exp(A.OpExp(o1, [e1]), join r1 r2)
  | r_exp_4 (S $ Cast(tp, r1) $ Exp(e,r2)) = S $ m_exp(A.Cast(tp, e), join r1 r2)

  (* default case: alrady reduced, must be last *)
  | r_exp_4 (S $ Exp(e,r)) = S $ Exp(e,r)

and p_ident ST = case first ST of
    T.IDENT(s) => ST |> drop >> push (Ident(Symbol.symbol s, here ST))
  | t => parse_error (here ST, "expected identifier, found " ^ t_toString t)

and p_fun_ident ST = case first ST of
    T.IDENT(s) => ST |> drop >> push (Ident(Symbol.symbol s, here ST))
  | t => parse_error (here ST, "expected function, found " ^ t_toString t
                               ^^ "address-of operator '&' can only be applied to functions")

and p_terminal t_needed ST = case first ST of
    t => if t_needed = t
         then ST |> shift
         else e_terminal (here ST, t_needed, t)

and p_terminal_h t_needed error_hint ST = case first ST of
    t => if t_needed = t
         then ST |> shift
         else error_expected_h (here ST, t_needed, t, error_hint)

(* error function for parsing terminal *)
and e_terminal (r, t_needed, t) = case t of
    T.EQ => error_expected_h (r, t_needed, t, "assignment l = e not permitted as expression; use '==' for comparison?")
  | T.PLUSPLUS => error_expected_h (r, t_needed, t, "increment l++ not permitted as expression")
  | T.MINUSMINUS => error_expected_h (r, t_needed, t, "decrement l-- not permitted as expression")
  | _ => error_expected (r, t_needed, t)

(* Top-level functions *)
fun parse_gdecls filename process_library process_file prelude token_front =
    let
        (* During initial parse, the second argument in A.UseLib
         * or A.UseFile will be NONE.  Once the library or filename
         * is processed (that is, parsed, checked, etc.) with the
         * process_library or process_file function, these resulting
         * global declarations are filled in.  Other pragmas are passed
         * through in raw form. *)
        fun process_pragma true (A.Pragma(A.UseLib(libname, NONE), ext)) =
              (A.Pragma(A.UseLib(libname, SOME(process_library libname)), ext),
               true)
          | process_pragma true (A.Pragma(A.UseFile(usefile, NONE), ext)) =
              (A.Pragma(A.UseFile(usefile, SOME(process_file filename usefile)), ext),
               true)
          | process_pragma true (gdecl as A.Pragma(_, _)) =
              (* unknown pragma; continue in prelude mode *)
              (gdecl, true)
          | process_pragma false (A.Pragma(A.UseLib _, ext)) =
              ( ErrorMsg.error ext ("#use directives must precede all other declarations")
              ; raise ErrorMsg.Error )
          | process_pragma false (A.Pragma(A.UseFile _, ext)) =
              ( ErrorMsg.error ext ("#use directives must precede all other declarations")
              ; raise ErrorMsg.Error )
          | process_pragma prelude gdecl =
              (* not a pragma, return prelude' = false *)
              (gdecl, false)
        val ST as (S, token_front') = p_gdecl (Bot, token_front)
        val () = if !ErrorMsg.anyErrors then raise ErrorMsg.Error else ()
    in  (* do not call 'first ST' below, because we do not want to look past EOL *)
        case ST
         of (Bot, M.Cons((T.EOF, r), ts')) => []
            (* nothing parsed, e.g., whole file already processed *)
          | (Bot $ GDecl(gdecl), _) =>
            let val _ = update_typetab gdecl (* update table of type names *)
                val (gdecl', prelude') = process_pragma prelude gdecl (* process #use pragmas *)
            in
                gdecl' :: parse_gdecls filename process_library process_file prelude' token_front'
            end
    end

(* parse filename process_library process_file = gdecls
 * parses all global declarations in filename.
 * Uses process_library function to handle #use <lib> pragmas and
 * process_file function to handle #use "file" pragmas.
 * Prints a message and raises ErrorMsg.Error if filename is not readable,
 * or there is a lexical or syntax error.
 *)
fun parse filename process_library process_file = 
    SafeIO.withOpenIn filename (fn instream =>
      let val _ = PS.pushfile filename (* start at pos 0 in filename *)
          val token_stream = C0Lex.makeLexer (fn _ => TextIO.input instream)
          val decls = parse_gdecls filename process_library process_file true (M.force token_stream)
          val _ = PS.popfile ()
      in decls end)
    handle e as IO.Io _ => ( ErrorMsg.error NONE (exnMessage e) ;
                             raise ErrorMsg.Error )

(* parse_stm token_front = SOME(s, token_front') where s is a complete statement,
 *                         and token_front' the remaining token stream
 * parse_stm token_front = NONE if the parse would be incomplete
 * raises ErrorMsg.Error if there is a lexing or parsing error.
 * The parsing state needs to be initialized before this function
 * is called so that error messages can convert character regions to
 * line.col form
 *)
fun parse_stm token_front =
    let
        val ST = p_stmt (Bot, token_front)
        val () = if !ErrorMsg.anyErrors then raise ErrorMsg.Error else ()
    in
        case ST (* do not use 'first ST', which might raise EOL *)
         of (Bot $ Stm(s,_), token_front') => SOME(s, token_front')
            (* tf' = M.Cons((t,_), ts') *)
            (* if t = T.EOL then there is no pending input, otherwise more can be parsed *)
            (* Nothing else should be possible *)
    end
    handle EOL => NONE (* incomplete parse; need to restart with more input *)

end
