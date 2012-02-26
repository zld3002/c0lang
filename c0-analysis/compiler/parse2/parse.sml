(* C0 Compiler
 * Parsing
 * Frank Pfenning <fp@cs.cmu.edu>
 *
 * Heavily modified by Nathan Snyder (npsnyder@andrew.cmu.edu)
 *
 * Now a hand-written LR parser
 *)

signature PARSE =
sig

  (* parse filename process_library process_file *)
  (* filename - the path to a C0 file that we will parse *)
  (* process_library - function for processing #use <...> pragmas *)
  (* process_file - function for processing #use "..." pragmas *)
  val parse: string 
             -> (string -> Ast.gdecl list) 
             -> (string -> string -> Ast.gdecl list) 
             -> Ast.program

  (* Interactive top-level hooks *)
  val parse_stm: 
      string 
      -> C0Lex.UserDeclarations.lexresult list 
      -> (C0Lex.UserDeclarations.lexresult list 
          * Ast.spec list 
          * Ast.stm 
          * Mark.ext) option
            
end

structure Parse :> PARSE =
struct

structure A = Ast
structure PS = ParseState
exception TODO of string
exception FatalError of string
exception No_Type
exception Ident_Not_TypeName of string

open C0Lex
open UserDeclarations

fun parse_error (s,(p1, p2)) = (ErrorMsg.error (PS.ext (p1,p2)) s;
                                raise ErrorMsg.Error)
fun fake_error (s,(p1, p2)) = (ErrorMsg.error (PS.ext (p1,p2)) s; ())

(* T for terminal, other types for each nonterminal *)
(* Various constants are automatically turned into <exp>s and don't need 
 * special tokens *)
datatype token 
  = T of lexresult
  | Gdecl of A.gdecl
  | Decls of A.vardecl list
  | Decl of A.vardecl
  | Params of A.vardecl list
  | Param of A.vardecl
  | Fields of A.field list
  | Annos of A.spec list
  | Stms of A.stm list
  | Stm of A.spec list * A.stm 
  | Simp of A.stm
  | LV of A.exp
  | Type of A.tp
  | Exp of A.exp
  | Args of A.exp list
  | SymIdent of A.ident
  | Oper of A.oper
  | Cond of A.exp
            
fun print_term t =
    case t  
     of RPAREN => ")"
      | LPAREN => "("
      | LBRACE => "{"
      | RBRACE => "}"
      | LBRACKET => "["
      | RBRACKET => "]"
      | SEMI => ";"
      | ARROW => "->"
      | DOT => "."
      | COLON => ":"
      | COMMA => ","
                 
      | WHILE => "while"
      | RETURN => "return"
      | BREAK => "break"
      | CONTINUE => "continue"
      | FOR => "for"
      | ELSE => "else"
      | IF => "if"
              
      | INT => "int"
      | STRING_TAU => "string"
      | CHAR => "char"
      | BOOL => "bool"
      | VOID => "void"
      | TYPENAME => "typename"
      | TYPEDEF => "typedef"
      | STRUCT => "struct"
                  
      | BS_OLD => "\\old"
      | BS_LENGTH => "\\length"
      | BS_RESULT => "\\result"
      | ASSERT => "assert"
      | LOOP_INVARIANT => "loop_invariant"
      | ENSURES => "ensures"
      | REQUIRES => "requires"
      | ANNO_END => "ANNO_END"
      | ANNO_BEGIN => "ANNO_BEGIN"
                      
      | MINUSMINUS => "--"
      | PLUSPLUS => "++"
      | GGEQ => ">>="
      | LLEQ => "<<="
      | BAREQ => "|="
      | CARETEQ => "^="
      | AMPEQ => "&="
      | PERCENTEQ => "%="
      | SLASHEQ => "/="
      | STAREQ => "*="
      | MINUSEQ => "-="
      | PLUSEQ => "+="
      | EQ => "="
              
      | TILDE => "~"
      | BANG => "!"
      | GG => ">>"
      | LL => "<<"
      | BAR => "|"
      | CARET => "^"
      | AMP => "&"
      | BARBAR => "||"
      | AMPAMP => "&&"
      | BANGEQ => "!="
      | EQEQ => "=="
      | GREATEREQ => ">="
      | GREATER => ">"
      | LESSEQ => "<="
      | LESS => "<"
      | PERCENT => "%"
      | SLASH => "/"
      | STAR => "*"
      | MINUS => "-"
      | PLUS => "+"
      | QUESTIONMARK => "?"
                        
      | IDENT => "ident"
      | VARNAME => "varname"
      | DECCONST => "decconst" 
      | HEXCONST => "hexconst" 
      | CHARCONST => "charconst"
      | STRINGCONST => "stringconst"
      | TRUE => "true"
      | FALSE => "false"
      | ALLOC_ARRAY => "alloc_array"
      | ALLOC => "alloc"
      | NULL => "NULL"
      | EOF => "eof"
      | PRAGMA => "#pragma"
(*      | _ => raise FatalError "Unknown terminal in print_term" *)

fun print_tok t =
    ((case t
       of (T((term, _, SOME(text))), _) => 
          (print (print_term term); print (" " ^ text))
        | (T((term, _, NONE)), _) => print (print_term term)
        | (Gdecl(_), _) => print "gdecl"
        | (Decls(_), _) => print "decls"
        | (Decl(_), _) => print "decl"
        | (Params(_), _) => print "params"
        | (Param(_), _) => print "param"
        | (Fields(_), _) => print "fields"
        | (Annos(_), _) => print "annos"
        | (Stms(_), _) => print "stms"
        | (Stm(_,_), _) => print "stm"
        | (Simp(_), _) => print "simp"
        | (LV(_), _) => print "LV"
        | (Type(_), _) => print "type"
        | (Exp(_), _) => print "exp"
        | (Args(_),_) => print "args"
        | (SymIdent(_), _) => print "symident"
        | (Oper(_), _) => print "oper"
        | (Cond(_), _) => print "condition")
     handle Unmatched => print "missing token"
   ; print "\n")

(* DemandEOF is raised for the interactive top-level parser only *)
exception DemandEOF 

fun location (NONE) = "_"
  | location (SOME(mark)) = Mark.show(mark)
fun mark (e, (left, right)) = A.Marked (Mark.mark' (e, PS.ext (left, right)))
fun marks (A.Assert(exp, nil), (left, right)) =
    let val ext = PS.ext (left, right)
    in
        case ext of NONE => 
                    (print "Why is a real thing not getting a mark?\n"
                     ; raise ErrorMsg.Error)
                  | SOME _ => (); 
	A.Markeds (Mark.mark' (A.Assert(exp, [A.StringConst(location ext ^ ": assert failed")]),
			       ext))
    end 
  | marks (s, (left, right)) = A.Markeds (Mark.mark' (s, PS.ext (left, right)))
                               
(* master_parse encapsulates all the local state needed to operate the parser,
 * which allows the parser to call itself recursively due to #use pragmas. *) 
fun master_parse filename lexer interactive = 
    let 
      (* Global stack variable for all parsing functions *)
      val stack : (token * (int * int)) list ref = ref []
      exception NoLexer
      val next : lexresult ref = ref (lexer ())

      (* Abbreviations *)
      val empty_stm = A.Seq([], [])

      (* Printing functions dependent on state *)
      fun print_stack_h toklist =
          case toklist  
           of t::rest => (print_tok t; print_stack_h rest)
            | [] => print "STACK END\n\n"

      fun print_stack (msg) = if false then (print (msg ^ "\n") ;
					     print_stack_h (!stack))
			      else ()

      (* Eats tokens without putting them on the stack *)
      fun get_next_token () = next := lexer ()

      fun push tok = stack := tok :: !stack
      fun cur_pos () = #1 (#2 (!next))
      fun cur_range () = (cur_pos (), cur_pos ())

      (* Push the next token on the stack and replace it *)
      fun shift () = (push (T(!next), #2(!next)); get_next_token ()) 
                     
      fun push_empty_stm () = 
          push (Stm (nil, marks (empty_stm, #2 (!next))), #2 (!next))

      fun demand (t, error_msg) =
          let
            val (term, pos, _) = !next
          in
            if term = EOF andalso interactive 
            then raise DemandEOF
            else if term = t 
            then get_next_token ()
            else
              (print ("Want: " ^ (print_term t) ^ "\n");
               print ("found: " ^ (print_term term) ^ "\n");
               parse_error (error_msg, #2(!next)))
          end

      (* MAIN PARSER FUNCTIONS *)

      fun parse_ident error_msg =
          let
            val (tok, pos, textOpt) = !next
            val _ = case tok
                     of IDENT => ()
                      | _ => parse_error (error_msg, pos)

            val SOME(name) = textOpt
            val name_sym = Symbol.symbol name
          in
            (push (SymIdent(name_sym), pos); get_next_token())
          end

      and parse_struct () = 
          let
            val _ = shift () (* STRUCT token *)
            val _ = parse_ident "Missing name in struct declaration"
            val (tok, pos, _) = !next
            val ok = case tok
                      of SEMI => true
                       | LBRACE =>
                         (get_next_token ();
                          parse_fields ();
                          demand (RBRACE, "Struct definition missing '}'");
                          true)
                       (* Check if we should be parsing  a function *)
                       | IDENT => false
                       | LBRACKET => false
                       | STAR => false
                       | _ => 
                         parse_error ("Bad token after struct name", pos)
          in
            if ok then 
              (demand (SEMI, "Struct declaration missing ';'");
               reduce_struct ())
            else
              recover_struct ()     
          end

      and reduce_struct () = 
          case !stack
           of [(SymIdent(sname),namepos), (T(STRUCT,_,_),structpos)] =>
              let
                val range = (#1 structpos, #2 namepos)
                val sdecl = A.Struct(sname, NONE, false, PS.ext range)
              in
                stack := [(Gdecl(sdecl), range)]
              end
            | [(Fields(fs),fpos), (SymIdent(sname),_), (T(STRUCT,_,_), spos)] =>
              let
                val range = (#1 spos, #2 fpos)
                val sdefn = A.Struct(sname, SOME(fs), false, PS.ext range)
              in
                stack := [(Gdecl(sdefn), range)]
              end
            | _ => parse_error ("Malformed struct", cur_range())

      (* This is called when, in the process of parsing a struct
       * declaration, we realize it was actually a function's return type.
       * To recover, we push a type onto the stack and then call parse_fun,
       * telling it that it doesn't need to parse a type. *)
      and recover_struct () = 
          case !stack
           of [(SymIdent(structname),npos), (T(STRUCT,_,_), spos)] => 
              (stack := [(Type(A.StructName(structname)),(#1 spos, #2 npos))];
               extend_type ();
               parse_fun false)
            | _ => raise FatalError "Bad stack in recover struct"
                         

      and parse_fields () = 
          if (#1 (!next)) = RBRACE then
            reduce_field_list ()
          else
            (parse_field (); parse_fields ())

      and reduce_field_list () =
          case !stack
           of (Fields(f2), f2pos)::(Fields(f1), f1pos)::rest =>
              (stack := (Fields(f1 @ f2), (#1 f1pos, #2 f2pos))::rest;
               reduce_field_list ())
            | (Fields(f), fpos)::rest => ()
            | _ => push (Fields([]), cur_range ())

      and parse_field () =
          let
            val _ = 
                if parse_type () then ()
                else
                  parse_error ("Bad type in field declaration", cur_range ())
            val _ = parse_ident "Missing field name in struct declaration\n"
            val _ = demand (SEMI, "Field missing semicolon\n")
          in
            reduce_field ()
          end

      and reduce_field () =
          case !stack 
           of (SymIdent(name), namepos)::(Type(t), tpos)::rest =>
              let
                val range = (#1 tpos, #2 namepos)
                val f = A.Field(name, t, PS.ext range)
              in
                stack := (Fields([f]), range)::rest
              end
            | _ => raise FatalError "Reduce field"
                         
      and parse_pragma () =
          let
	    val (PRAGMA, range, SOME(line)) = !next
            (* val () = print ("PRAGMA:\n" ^ line ^ "\n") *)
	    val ast = 
                A.Pragma (ParsePragma.parse_pragma line (PS.ext range),
                          PS.ext range)
	    val _ = get_next_token ()
          in
	    stack := [(Gdecl(ast), range)]
          end

      and parse_typedef () = 
          let
            val _ = shift () (* TYPEDEF *)
            val _ = if parse_type () then ()
                    else
                      parse_error ("Bad type in typedef", cur_range ())
            val _ = parse_ident "Missing new type name in typedef"
            val _ = demand (SEMI, "Typedef missing semicolon")
          in
            reduce_typedef ()
          end

      and reduce_typedef () =
          case !stack
           of [(SymIdent(id), idpos),
               (Type(tau), _), 
               (T(TYPEDEF,_,_), tdpos)] =>
              let
                val range = (#1 tdpos, #2 idpos)
              in
                stack := [(Gdecl(A.TypeDef(id, tau, PS.ext range)), range)]
              end
            | _ => raise FatalError "Malformed typedef"

      and parse_type () = 
          let
            val (tok, pos, text) = !next
            val tp = case tok
                      of INT => A.Int
                       | CHAR => A.Char
                       | STRING_TAU => A.String
                       | BOOL => A.Bool
                       | STRUCT => parse_struct_type ()
                       | IDENT => parse_ident_type ()
                       | VOID => A.Void
                       | _ => raise No_Type
          in
            (push (Type(tp), pos); 
             get_next_token();
             extend_type ();
             true)
          end
          handle No_Type => false
	       | Ident_Not_TypeName(id) => 
		 (* potential type starts with identifier which is
                  * not a type name.  This will have to return false
                  * or signal an error.  We check if it is has form
		  * ID ID, ID LBRACKET RBRACKET, ID STAR STAR, ID STAR LBRACKET
                  * none of which can start an expression and must therefore
                  * be an error: type name s undefined
                  *)
		 false (* for now! *)

      (* This function is weird in that it actually returns the type
       * it parses instead of pushing it onto the stack *)
      and parse_struct_type () = 
          let
            val _ = get_next_token () (* Clear struct token *)
            val (tok, pos, text) = !next
          in
            case (tok, text)
             of (IDENT, SOME(name)) => A.StructName(Symbol.symbol name)
              | _ => parse_error ("Invalid struct name\n", pos)
          end

      and parse_ident_type () =
          let
            val (IDENT, pos, SOME(name)) = !next
            val s = Symbol.symbol name
          in 
            case Typetab.lookup s
             of NONE => raise Ident_Not_TypeName(name)
              | SOME _ => A.TypeName(s)
          end

      and extend_type () =
          let
            val (tok, pos, _) = !next
          in
            case (tok, !stack)
             of (STAR, (Type(tau),taupos)::rest) =>
                (stack := (Type(A.Pointer(tau)), (#1 taupos, #2 pos))::rest;
                 get_next_token ();
                 extend_type ())
              | (LBRACKET, (Type(tau), taupos)::rest) =>
                (get_next_token();
		 demand (RBRACKET, "Expected ']' in array type");
		 stack := (Type(A.Array(tau)), (#1 taupos, #2 pos))::rest;
                 extend_type ())
              | _ => ()
          end

      and parse_fname () =
          case !next
           of (IDENT, pos, SOME(text)) =>
              (stack := (SymIdent(Symbol.symbol text), pos) :: !stack;
               get_next_token ())
            | (_, pos, _) => parse_error ("Function name missing", pos) 

      and parse_params () =
          let
            val _ = demand (LPAREN, "Missing '(' in function declaration")
            val _ = parse_params_first ()
            val _ = demand (RPAREN, "Missing ')' in function declaration")
          in
            reduce_params ()
          end

      and parse_params_first () =
          case #1 (!next)
           of RPAREN => ()
            | _ => (parse_param (); parse_params_next ())

      and parse_params_next () =
	  case #1 (!next)
	   of COMMA => (get_next_token (); parse_param (); parse_params_next ())
            | RPAREN => ()
            | _ => parse_error ("Expected ',' or ')' in function declaration", cur_range ())

      and parse_param () =
          let
            val _ = if parse_type () then ()
                    else
                      parse_error ("Parameter missing type", cur_range ())
            val (tok, pos, textOpt) = !next
          in
            case (tok, textOpt)
             of (IDENT, SOME(text)) =>
                (push (SymIdent(Symbol.symbol text), pos);
                 reduce_param ();
                 get_next_token())
              | _ => parse_error ("Missing parameter name", pos)
          end

      and parse_annos () = 
          if (#1 (!next)) = ANNO_BEGIN then
            (shift (); parse_annos_helper ())
          else
            ()

      and parse_annos_helper () =
          if #1 (!next) = ANNO_END then
            (get_next_token ();
             if #1 (!next) = ANNO_BEGIN then
               (get_next_token ();
                parse_annos_helper ())
             else
               reduce_annos ())
          else
            (parse_anno (); parse_annos_helper ())
            
      and parse_anno () =
          let
            val (tok, pos, text) = !next
          in
            case tok
             of REQUIRES => parse_requires ()
              | ENSURES => parse_ensures ()
              | LOOP_INVARIANT => parse_loop_invariant ()
              | ASSERT => parse_anno_assert ()
              | _ => parse_error ("Invalid annotation", pos)
          end

      and parse_requires () = 
          let
            val _ = shift ()
            val _ = parse_exp ()
            val _ = demand (SEMI, "Missing ';' in 'requires' annotation")
          in
            reduce_requires ()
          end

      and reduce_requires () =
          case !stack
           of (Exp(e), epos)::(T(REQUIRES,_,_), rpos)::rest =>
              let
                val range = (#1 rpos, #2 epos)
                val anno = A.Requires(e, PS.ext range)
              in 
                stack := (Annos([anno]), range)::rest
              end
            | _ => raise FatalError "Malformed requires"

      and parse_ensures () = 
          let
            val _ = shift ()
            val _ = parse_exp ()
            val _ = demand (SEMI, "Missing ';' in 'ensures' annotation")
          in
            reduce_ensures ()
          end

      and reduce_ensures () =
          case !stack
           of (Exp(e), epos)::(T(ENSURES,_,_), spos)::rest =>
              let
                val range = (#1 spos, #2 epos)
                val anno = A.Ensures(e, PS.ext range)
              in 
                stack := (Annos([anno]), range)::rest
              end
            | _ => raise FatalError "Malformed ensures"

      and parse_loop_invariant () =
          let
            val _ = shift ()
            val _ = parse_exp ()
            val _ = demand (SEMI, "Missing ';' in 'loop invariant' annotation")
          in
            reduce_loop_invariant ()
          end

      and reduce_loop_invariant () =
          case !stack
           of (Exp(e), epos)::(T(LOOP_INVARIANT,_,_), spos)::rest =>
              let
                val range = (#1 spos, #2 epos)
                val anno = A.LoopInvariant(e, PS.ext range)
              in 
                stack := (Annos([anno]), range)::rest
              end
            | _ => raise FatalError "Malformed loop invariant"

      and parse_anno_assert () = 
          let
            val _ = shift ()
            val _ = parse_exp ()
            val _ = demand (SEMI, "Missing ';' in 'assert' annotation")
          in
            reduce_anno_assert ()
          end

      and reduce_anno_assert () =
          case !stack
           of (Exp(e), epos)::(T(ASSERT,_,_), spos)::rest =>
              let
                val range = (#1 spos, #2 epos)
                val anno = A.Assertion(e, PS.ext range)
              in 
                stack := (Annos([anno]), range)::rest
              end
            | _ => raise FatalError "Malformed assert annotation"


      and parse_annos_force () =
          if #1 (!next) = ANNO_BEGIN then
            parse_annos ()
          else
            push (Annos([]), cur_range())

      and reduce_annos () = 
          case !stack 
           of (Annos(a2),a2pos)::(Annos(a1),a1pos)::rest =>
              (stack := (Annos(a1@a2), (#1 a1pos, #2 a2pos))::rest; 
               reduce_annos ())
            | (Annos(a),apos)::(T(ANNO_BEGIN,_,_),_)::rest => 
              stack := (Annos(a), apos)::rest
	    | (T(ANNO_BEGIN,_,_),_)::rest =>
	      stack := (Annos([]), cur_range())::rest
            | _ => parse_error ("Internal parser error: missing ANNO_BEGIN", 
                                cur_range())

      and parse_decl_line () =
          let
            val _ = if parse_type () then () else raise No_Type
            val (tok, pos, text) = !next
            val _ =
                case (tok, text)
                 of (IDENT, SOME(name)) => 
                    (push (SymIdent(Symbol.symbol name), pos);
                     get_next_token())
                  | _ => 
                    if tok = EOF andalso interactive 
                    then raise DemandEOF
                    else parse_error ("Missing variable name in declaration",
                                      pos)

            val _ =
                case #1 (!next)
                 of EQ =>  (get_next_token (); parse_exp ())
                  | COMMA => parse_error ("Multiple variable names" ^
                                          "in a single declaration", pos)
                  | _ => ()

	  (* SEMI is now demanded elsewhere *)
          (*
           val _ = demand(SEMI, "Variable declaration missing semicolon") 
           *)
          in
            (reduce_decl (); true)
          end
          handle No_Type => false

      and reduce_decl () =
          case !stack
           of (Exp(e), epos)::(SymIdent(s),_)::(Type(t), tpos)::rest =>
              let
                val range = (#1 tpos, #2 epos)
                val ext = PS.ext range
              in
                stack := (Decl(A.VarDecl(s, t, SOME(e), ext)), range)::rest
              end
            | (SymIdent(s), spos)::(Type(t), tpos)::rest =>
              let
                val range = (#1 tpos, #2 spos)
                val ext = PS.ext range
              in
                stack := (Decl(A.VarDecl(s, t, NONE, ext)), range)::rest
              end
            | _ =>
              parse_error ("Malformed variable declaration", cur_range())

      (*
       and parse_decls () = 
           if parse_decl_line () then
             parse_decls ()
           else
             reduce_decls ()
       *)

      and parse_statements () = 
          case #1 (!next)
           of RBRACE => reduce_statements ()
            | _ => (parse_statement (); parse_statements ())

      and parse_standalone_statement () = 
          (parse_annos_force ();
           parse_statement ();
           case !stack
             of (Stm(annos2, s), spos) :: (Annos(annos1), apos) :: [] =>
		let
		    val range = (#1 apos, #2 spos)
		    val SOME(pos) = PS.ext range
		in
		    (annos1 @ annos2, s, pos)
		end
              | _ => parse_error ("Malformed single statement", cur_range()))
           
      and parse_statement () = 
          let 
            val (tok, pos, _) = !next
          in
            case tok
             of RETURN => parse_return () 
              | WHILE => parse_while ()
              | IF => parse_if ()
              | FOR => parse_for ()
              | ASSERT => parse_assert ()
              | LBRACE => parse_body ()
              | CONTINUE => 
                (get_next_token();
                 demand(SEMI, "Missing semicolon at statement\n");
                 push (Stm(nil, marks (A.Continue, pos)), pos))
              | BREAK => 
                (get_next_token();
                 demand(SEMI, "Missing semicolon at statement\n");
                 push (Stm(nil, marks (A.Break, pos)), pos))
              | SEMI => (print ("Do not terminate conditionals, loops, or blocks by semicolon\n");
			 print ("Use {} as empty statement\n");
			 parse_error("Unexpected semicolon ';'", pos))
              (* removed Jan 30, 2011 *)
              (* | SEMI => (push_empty_stm (); get_next_token()) *)
              | ANNO_BEGIN =>
                (parse_annos ();
                 parse_statement ();
                 case !stack
                  of (Stm(annos2, s), dpos)::(Annos(annos1), apos)::rest =>
		       stack := (Stm(annos1 @ annos2, s), (#1 apos, #2 dpos))
				:: rest
		   | (Stm(annos, s),spos)::rest => ()
                   | _ => raise FatalError "anno statement"
                )
              | _ => (parse_simple ();
                      demand (SEMI, "Missing semicolon in simple statement"))
          end

      and parse_simple () = 
          if parse_decl_line ()
          then reduce_simp ()
          else 
            let
              val began_with_star = #1 (!next) = STAR 
              val _ = parse_exp ()
              val _ =
                  if #1 (!next) = PLUSPLUS then
                    if began_with_star then
                      parse_error ("For compatibility with C, " 
                                   ^ "please write (*e)++; instead of *e++;", 
                                   cur_range ())
                    else
                      shift ()
                  else
                    ()

              val _ =
                  if #1 (!next) = MINUSMINUS then
                    if began_with_star then
                      parse_error ("For compatibility with C, " 
                                   ^ "please write (*e)--; instead of *e--;",
                                   cur_range ())
                    else
                      shift ()
                  else
                    ()

              val _ = if is_asnop (#1 (!next)) then
                        (shift (); parse_exp ())
                      else
                        ()
                        
            in
              reduce_simp ()
            end

      and reduce_simp () =
          case !stack
           of (T(PLUSPLUS,_,_), ppos)::(Exp(e), epos)::rest =>
              let
                val range = (#1 epos, #2 ppos)
                val one = A.IntConst(Word32.fromInt(1))
                val stm = marks (A.Assign (SOME(A.PLUS), e, one), range)
              in
                stack := (Stm(nil, stm), range)::rest
              end
            | (T(MINUSMINUS,_,_), ppos)::(Exp(e), epos)::rest =>
              let
                val range = (#1 epos, #2 ppos)
                val one = A.IntConst(Word32.fromInt(1))
                val stm = marks (A.Assign (SOME(A.MINUS), e, one), range)
              in
                stack := (Stm(nil, stm), range)::rest
              end
            | (Exp(e), epos)::(tail as (T(tok,_,_),_)::(Exp(lv), lvpos)::rest) =>
	      if is_asnop tok
	      then 
		  let
                      val range = (#1 lvpos, #2 epos)
                      val operopt = get_asnop tok
                      val stm = marks (A.Assign (operopt, lv, e), range)
		  in
                      stack := (Stm(nil, stm), range)::rest
		  end
	      else
		  stack := (Stm(nil, marks (A.Exp(e), epos)), epos)::tail
            | (Exp(e), epos)::rest =>
              stack := (Stm(nil, marks (A.Exp(e), epos)), epos)::rest
            | (Decl(d), dpos)::rest =>
	      stack := (Stm(nil, A.StmDecl(d)), dpos)::rest
            | _ => parse_error ("Malformed simp", cur_range())

      (* anno_stm (Stm(annos, s)) invoke only then scope of s is finalized *)
      and anno_stm (Stm(nil, A.StmDecl(d))) =
	    A.Seq([d], [])
        | anno_stm (Stm(nil, s)) =
	    s
	| anno_stm (Stm(annos, A.StmDecl(d))) =
	    A.Seq([], [A.Anno(annos), A.Seq([d], [])])
	| anno_stm (Stm(annos, s)) =
	    A.Seq([], [A.Anno(annos)] @ [s])
                   
      and is_asnop tok = 
          if tok = EQ then
            true
          else
            case get_asnop tok
             of SOME(_) => true
              | NONE => false

      and get_asnop asnop =
          case asnop
           of EQ => NONE
            | PLUSEQ => SOME(A.PLUS)
            | MINUSEQ => SOME(A.MINUS)
            | STAREQ => SOME(A.TIMES)
            | SLASHEQ => SOME(A.DIVIDEDBY)
            | PERCENTEQ => SOME(A.MODULO)
            | AMPEQ => SOME(A.AND)
            | CARETEQ => SOME(A.XOR)
            | BAREQ => SOME(A.OR)
            | LLEQ => SOME(A.SHIFTLEFT)
            | GGEQ => SOME(A.SHIFTRIGHT)
            | _ => NONE

      and parse_if () = 
          let
            val _ = shift ()
            val _ = demand (LPAREN, "Missing '(' in if statement condition")
            val _ = parse_exp ()
            val _ = demand (RPAREN, "Missing ')' in if statement condition")
	    val _ = reduce_condition ()  (* so while (e) *x = e; parses ok *)
            val _ = parse_statement ()

            (* Grab an else statement if one is present *)
            val _ = case #1 (!next)
                     of ELSE => (shift (); parse_statement ())
                      | _ => ()
          in
            reduce_if ()
          end

      and reduce_condition () =
	  case !stack
	   of (Exp(cond), pos)::rest => (stack := (Cond(cond), pos)::rest)
            | (_, pos)::rest => parse_error("Malformed condition", pos)

      and reduce_if () =
	  (print_stack("reduce_if") ; 
          case !stack
           of (Stm(annos2, s2), s2pos)::
              (T(ELSE,_,_),_)::
              (Stm(annos1, s1), _)::
              (Cond(cond), condpos)::
              (T(IF,_,_), ifpos)::
              rest
              => let
		  val s1' = anno_stm (Stm(annos1, s1))
		  val s2' = anno_stm (Stm(annos2, s2))
                val range = (#1 ifpos, #2 s2pos)
                val stm = marks (A.If(mark (cond, condpos), s1', s2'), range)
              in
                stack := (Stm(nil,stm), range)::rest
              end

            | (Stm(annos1, s1), s1pos)::
              (Cond(cond),_)::
              (T(IF,_,_), ifpos)::
              rest
              => let
		  val s1' = anno_stm (Stm(annos1, s1))
                val range = (#1 ifpos, #2 s1pos)
                val stm = marks (A.If(cond, s1, empty_stm), range)
              in
                stack := (Stm(nil, stm), range)::rest
              end
            | _ => parse_error ("Malformed if statement\n", cur_range()))


      and parse_for () = 
          let
            val _ = shift () (* FOR token *)
            val _ = demand (LPAREN, "Missing '(' in for loop")
            val _ = case #1 (!next)
                     of SEMI => push_empty_stm ()
                      | _ => parse_simple ()
            val _ = demand (SEMI, "Missing ';' in for loop conditions")
            val _ = parse_exp ()
            val _ = demand (SEMI, "Missing ';' in for loop conditions")
            val _ = case #1 (!next)
                     of RPAREN => push_empty_stm ()
                      | _ => parse_simple ()
            val _ = demand (RPAREN, "Missing ')' in for loop")
            val _ = parse_loop_body ()
          in
            reduce_for ()
          end

      and reduce_for () =
          case !stack 
           of (Stm(annos2, body), bodypos)::
	      (Annos(annos1), apos)::
              (Stm(nil, update), _)::
              (Exp(cond), condpos)::
              (Stm(nil, init),_)::
              (T(FOR,_,_), forpos)::
              rest
              => let
                val range = (#1 forpos, #2 bodypos)
                val cond' = mark (cond, condpos)
                val stm = marks (A.For(init, cond', update, annos1 @ annos2, body), range)
              in
                stack := (Stm(nil,stm), range)::rest
              end
            | _ => parse_error ("Malformed for loop\n", cur_range())

      and parse_assert () = 
          let
            val _ = shift () (* The ASSERT token *)
            val _ = demand (LPAREN, "Missing '(' in assert")
            val _ = parse_exp ()
            val _ = demand (RPAREN, "Missing ')' in assert")
            val _ = demand (SEMI, "Missing ';' in assert statement")
          in
            reduce_assert ()
          end

      and reduce_assert () =
          case !stack 
           of (Exp(e1), e1pos)::(T(ASSERT,_,_), apos)::rest =>
              let
                val range = (#1 apos, #2 e1pos)
                val stm = marks (A.Assert(e1, nil), range)
              in
                stack := (Stm(nil,stm), range)::rest
              end
            | _ => parse_error ("Malformed assert statement\n", cur_range())

      and parse_while () =
          let
            val _ = shift () (* Shift while terminal to stack *)
            val _ = demand (LPAREN, "Missing '(' at while loop condition")
            val _ = parse_exp ()
            val _ = demand (RPAREN, "Missing ')' at while loop condition")
	    val _ = reduce_condition () (* so while (e) *x = e; parses ok *)
            val _ = parse_loop_body ()
          in
            reduce_while ()
          end
          
      and reduce_while () =
          case !stack 
           of (Stm(annos2, b), bpos)::(Annos(annos1), apos)::(Cond(c), cpos)::(T(WHILE, _, _), wpos)::rest =>
              let
                val range = (#1 wpos, #2 bpos)
                val stm = marks (A.While(mark (c, cpos), annos1 @ annos2, b), range)
              in
                stack := (Stm(nil,stm), range)::rest
              end
            | _ => parse_error ("Malformed while loop\n", cur_range())
		   
      and parse_return () =
          let
            val _ = shift () (*Shift the RETURN onto the stack *)
            val _ = case #1 (!next)
                     of SEMI => ()
                      | _ => parse_exp ()

            val _ = demand (SEMI, "Statement not terminated with a ';'")
          in
            reduce_return ()
          end

      and reduce_return () = 
          case !stack
           of (Exp(e), epos)::(T(RETURN, _, _), rpos)::rest =>
              let
                val range = (#1 rpos, #2 epos)
                val stm = marks (A.Return(SOME(e)), range)
              in
                stack := (Stm(nil, stm), range)::rest
              end
            | (T(RETURN, _, _), rpos) :: rest =>
              stack := (Stm(nil, marks (A.Return(NONE), rpos)), rpos)::rest
            | _ =>
              parse_error ("Invalid return statement", cur_range ()) 

      and parse_decnum () =
          let
            val (DECCONST, pos, SOME(text)) = !next
          in let val _ =
                     case Word32Signed.fromString text
                      of NONE => parse_error("Cannot parse integer constant "
                                             ^ text, pos)
                       | SOME(n) => (push (Exp(A.IntConst(n)), pos);
                                     get_next_token()) 
             in () end
             handle Overflow => 
                    parse_error("Integer constant " ^ text ^ " out of range", 
                                #2 (!next))
          end

      and parse_hexnum () =
          let
            val (HEXCONST, pos, SOME(text)) = !next
          in let val _ =
                     case Word32Signed.fromHexString text
                      of NONE => parse_error("Cannot parse integer constant " 
                                             ^ text, pos)
                       | SOME(n) => (push (Exp(A.IntConst(n)), pos);
                                     get_next_token()) 
             in () end
             handle Overflow => 
                    parse_error("Integer constant " ^ text ^ " out of range", 
                                #2 (!next))
          end

      and parse_char_const () =
          let
            val (CHARCONST, pos, text) = !next
            val SOME(ctext) = text
            val cOpt = C0Char.fromC0String(ctext)
            val c =
                case cOpt
                 of SOME(c) => c
                  | NONE => parse_error ("Malformed character '" ^ ctext ^ "'", pos)
          in
            (push (Exp(mark (A.CharConst(c), pos)), pos);
             get_next_token())
          end

      and parse_string_const () =
          let
            val (STRINGCONST, pos, SOME(s)) = !next
            val exp = mark (A.StringConst(s), pos)
          in
            (get_next_token (); push (Exp(exp), pos))
          end

      and binop_from_tok tok =
          case tok 
           of STAR=> A.TIMES
            | SLASH => A.DIVIDEDBY
            | PERCENT => A.MODULO
            | PLUS => A.PLUS
            | MINUS => A.MINUS
            | LL => A.SHIFTLEFT
            | GG => A.SHIFTRIGHT
            | LESS => A.LESS
            | LESSEQ => A.LEQ
            | GREATER => A.GREATER
            | GREATEREQ => A.GEQ
            | EQEQ => A.EQ
            | BANGEQ => A.NOTEQ
            | AMP => A.AND
            | CARET => A.XOR
            | BAR => A.OR
            | AMPAMP=> A.LOGAND
            | BARBAR => A.LOGOR
            | _ => parse_error ("Bad operation in exp binop exp", cur_range())

      and parse_exp () = 
          let 
            val (term, pos, text) = !next
            val _ =
                case term
                 of DECCONST => parse_decnum ()
                  | HEXCONST => parse_hexnum ()
                  | TRUE =>
                    (push (Exp(mark (A.True, pos)), pos); get_next_token())
                  | FALSE => 
                    (push (Exp(mark (A.False, pos)), pos); get_next_token())
                  | NULL => 
                    (push (Exp(mark (A.Null, pos)), pos); get_next_token ())
                  | CHARCONST => parse_char_const ()
                  | STRINGCONST => parse_string_const ()
                  | IDENT => parse_exp_ident ()
                  | LPAREN => parse_paren_exp ()
                  | RPAREN =>  parse_error ("Unmatched ')'", pos)
                  | BS_RESULT => 
                    (push (Exp(mark (A.Result, pos)), pos); get_next_token ())
                  | BS_LENGTH => parse_bslength ()
                  | BS_OLD => parse_bsold ()
                  | MINUS => 
                    (push (Oper(A.NEGATIVE), pos); get_next_token (); 
                     parse_exp ())
                  | STAR => 
                    (push (Oper(A.DEREF), pos); get_next_token (); parse_exp ())
                  | ALLOC => parse_alloc ()
                  | ALLOC_ARRAY => parse_alloc_array ()
                  | BANG => 
                    (push (Oper(A.LOGNOT), pos); get_next_token (); 
                     parse_exp ())
                  | TILDE => 
                    (push (Oper(A.COMPLEMENT), pos); get_next_token (); 
                     parse_exp ())
                  | EOF =>
		    if interactive then raise DemandEOF
		    else parse_error("Unexpected end of file; unmatched '{', '(', or '[' ?\n", pos)
                  | _ => 
                    if term = EOF andalso interactive then raise DemandEOF
                    else parse_error ("Invalid character " ^ print_term term ^
                                      " at expression beginning\n", pos)
          in
            continue_exp ()
          end

      and continue_exp () =
          let
            val (term, pos, text) = !next
            val should_continue = ref true
            val _ =
                case term
                 (* Postfix operators *)
                 of LBRACKET => parse_array_access ()
                  | ARROW => parse_arrow ()
                  | DOT => parse_dot ()
                  | QUESTIONMARK => (reduce_exp (); parse_ternary())
                  (* Binops *)
                  | PLUS => parse_binop ()
                  | MINUS => parse_binop ()
                  | STAR => parse_binop ()
                  | SLASH => parse_binop ()
                  | PERCENT => parse_binop ()
                  | LESS => parse_binop ()
                  | LESSEQ => parse_binop ()
                  | GREATER => parse_binop ()
                  | GREATEREQ => parse_binop ()
                  | EQEQ => parse_binop ()
                  | BANGEQ => parse_binop ()
                  | AMPAMP => parse_binop ()
                  | BARBAR => parse_binop ()
                  | AMP => parse_binop ()
                  | CARET => parse_binop ()
                  | BAR => parse_binop ()
                  | LL => parse_binop ()
                  | GG => parse_binop ()
                  (*| _ => should_continue := false *)
                          
                  (* Things which may legitimately follow an expression *)
                  | RPAREN => should_continue := false
                  | SEMI => should_continue := false
                  | COMMA => should_continue := false
                  | RBRACKET => should_continue := false
                  | PLUSPLUS => should_continue := false
                  | MINUSMINUS => should_continue := false
                  | EQ => should_continue := false
                  | GGEQ => should_continue := false
                  | LLEQ => should_continue := false
                  | BAREQ => should_continue := false
                  | CARETEQ => should_continue := false
                  | AMPEQ => should_continue := false
                  | PERCENTEQ => should_continue := false
                  | SLASHEQ => should_continue := false
                  | STAREQ => should_continue := false
                  | MINUSEQ => should_continue := false
                  | PLUSEQ => should_continue := false
                  | COLON => should_continue := false

                  (* Anything else must be an error *)
                  | _ => 
                    (if term = EOF andalso interactive 
                     then raise DemandEOF
                     else parse_error ("Malformed expression", cur_range ())
                    (* TODO: get better positioning *))
                         
          in
            if !should_continue then
              continue_exp ()
            else
              reduce_exp ()
          end

      and reduce_exp () =
          case !stack
           of (Exp(e2),e2pos)::(Oper(binop),_)::(Exp(e1),e1pos)::rest =>
              let
                val range = (#1 e1pos, #2 e2pos)
                val exp = mark (A.OpExp(binop, [e1, e2]), range)
              in
                (stack := (Exp(exp), range)::rest; reduce_exp ())
              end
            | (Exp(e), epos)::(Oper(unop), oppos)::rest =>
              let
                val range = (#1 oppos, #2 epos)
                val exp = mark (A.OpExp(unop, [e]), range)
              in
                (stack := (Exp(exp), range)::rest; reduce_exp ())
              end
            | (Exp(e),_)::rest =>
              ()
            | _ => raise FatalError "reduce_exp"

      and parse_paren_exp () =
          let
            val (LPAREN, lpos, _) = !next
            val _ = shift ()
            val _ = parse_exp ()
            val _ = case #1 (!next)
                     of RPAREN => get_next_token ()
                      | _ => parse_error ("Unmatched '('", lpos)
          in
            case !stack
             of e::(T(LPAREN,_,_),_)::rest =>
                stack := e::rest
          end

      and parse_binop () =
          case !stack 
           of (Exp(e2),e2pos)::(Oper(binop),_)::(Exp(e1),e1pos)::rest =>
              let
                val (term, pos, _) = !next
                val new_oper = binop_from_tok term
                val prec_old = precedence binop
                val prec_new = precedence new_oper
              in
                if prec_old >= prec_new then
                  let
                    val range = (#1 e1pos, #2 e2pos)
                    val exp = mark (A.OpExp(binop, [e1, e2]), range)
                  in
                    (stack := (Exp(exp), range)::rest; parse_binop ())
                  end
                else
                  let
                    val (binop, pos, _) = !next
                    val _ = push (Oper(new_oper), pos)
                    val _ = get_next_token ()
                  in
                    parse_exp ()
                  end
              end
            | (Exp(e),epos)::(Oper(unop),oppos)::rest =>
              let
                (* All unops have higher precedence than all binops *)
                val range = (#1 oppos, #2 epos)
                val exp = mark (A.OpExp(unop, [e]), range)
                val _ = stack := (Exp(exp), range)::rest
              in
                parse_binop ()
              end
            | (Exp(e), epos)::rest =>
              let
                val (binop, pos, _) = !next
                val _ = push (Oper(binop_from_tok binop), pos)
                val _ = get_next_token ()
              in
                parse_exp ()
              (* This will call continue_exp which will eventually
                      reduce the binop to a single expression *)
              end
            | _ => raise FatalError "parse_binop"

      and precedence binop =
          case binop
           of A.LOGOR => 1
            | A.LOGAND => 2
            | A.OR => 3
            | A.XOR => 4
            | A.AND => 5
            | A.EQ => 6
            | A.NOTEQ => 6
            | A.LESS => 7
            | A.LEQ => 7
            | A.GREATER => 7
            | A.GEQ => 7
            | A.SHIFTLEFT => 8
            | A.SHIFTRIGHT => 8
            | A.PLUS => 9
            | A.MINUS => 9
            | A.TIMES => 10
            | A.DIVIDEDBY => 10
            | A.MODULO => 10
            | _ => raise FatalError "precedence"


      and parse_exp_ident () = 
          let
            val (IDENT, pos, SOME(name)) = !next
            val s = Symbol.symbol name
            val _ = get_next_token ()
            val (tok,_,_) = !next
          in
            case tok
             of LPAREN => (push (SymIdent(s), pos);  parse_funcall ())
              | _ => push (Exp(mark (A.Var(s), pos)), pos)
          end

      and parse_funcall () =
          let
            val _ = get_next_token () (* LPAREN *)
            val _ = parse_call_args ()
            val _ = demand (RPAREN, "Function call missing ')'")
          in
            reduce_funcall ()
          end

      and reduce_funcall () = 
          case !stack 
           of (Args(args), argspos)::(SymIdent(fname), namepos)::rest =>
              let
                val range = (#1 namepos, #2 argspos)
                val callexp = mark (A.FunCall(fname, args), range)
              in
                stack := (Exp(callexp), range)::rest
              end
            | _ => raise FatalError "function call"
      (*(print_stack (); parse_error ("Bad function call", cur_range ())) *)

      and parse_call_args () = 
          case #1 (!next)
            of COMMA => raise parse_error ("Extra comma", #2 (!next))
             | RPAREN => push (Args([]), (cur_pos (), cur_pos ()))
             | _ => parse_arg ()

      and parse_call_args_helper () = 
          case #1 (!next)
           of RPAREN => (push (Args([]), (cur_pos (), cur_pos ())); 
                         reduce_args ())
            | COMMA => (get_next_token (); parse_arg ())
            | _ => parse_error ("Bad arguments - possibly a missing comma", cur_range ())

      and parse_arg () =
          let
            val _ = parse_exp ()
            val _ = reduce_args ()
          in
            parse_call_args_helper ()
          end

      and reduce_args () =
          case !stack
           of (Exp(newarg), epos)::(Args(args), argspos)::rest =>
              stack := (Args(args@[newarg]), (#1 argspos, #2 epos))::rest
            | (Exp(arg), argpos)::rest =>
              stack := (Args([arg]), argpos)::rest
            | (Args(args2), args2pos)::(Args(args1), args1pos)::rest =>
              stack := (Args (args1@args2), (#1 args1pos, #2 args2pos))::rest
            | (Args(_),_)::rest => ()
            | _ => raise FatalError "reduce_args"

      and parse_bslength () =
          let
            val _ = shift ()
            val _ = demand (LPAREN, "length missing '('")
            val _ = parse_exp ()
            val _ = demand (RPAREN, "length missing ')'")
          in
            reduce_bslength ()
          end

      and reduce_bslength () =
          case !stack 
           of (Exp(e), epos)::(T(BS_LENGTH,_,_), lpos)::rest =>
              let
                val range = (#1 lpos, #2 epos)
              in
                stack := (Exp(mark (A.Length(e), range)), range)::rest
              end
            | _ => raise FatalError "bslength"

      and parse_bsold () =
          let
            val _ = shift ()
            val _ = demand (LPAREN, "length missing '('")
            val _ = parse_exp ()
            val _ = demand (RPAREN, "length missing ')'")
          in
            reduce_bsold ()
          end

      and reduce_bsold () =
          case !stack 
           of (Exp(e), epos)::(T(BS_OLD,_,_),opos)::rest =>
              let 
                val range = (#1 opos, #2 epos)
              in
                stack := (Exp(mark (A.Old(e), range)), range)::rest
              end
            | _ => raise FatalError "bsold"

      and parse_deref () =
          let
            val _ = shift ()
            val _ = parse_exp ()
          in
            reduce_deref ()
          end
      and reduce_deref () =
          case !stack
           of (Exp(e), epos)::(T(STAR,_,_), starpos)::rest =>
              let
                val range = (#1 starpos, #2 epos)
                val exp = mark (A.OpExp (A.DEREF, [e]), range)
              in
                stack := (Exp(exp), range)::rest
              end
            | _ => raise FatalError "Malformed deref"

      and parse_array_access () = 
          let
            val _ =
                case !stack
                 of (Exp(_),_)::_ => ()
                  | _ => parse_error ("Array access missing array expression",
                                      cur_range ())
            val _ = shift () (* shift LBRACKET *)
            val _ = parse_exp ()
            val _ = demand (RBRACKET, "Array access missing ']'")
          in
            reduce_array_access ()
          end

      and reduce_array_access () =
          case !stack
           of (Exp(index), indexpos) 
              ::(T(LBRACKET,_,_),_)
              ::(Exp(array), arraypos)
              ::rest =>
              let
                val range = (#1 arraypos, #2 indexpos)
                val exp = mark (A.OpExp(A.SUB, [array, index]), range)
              in
                stack := (Exp(exp), range)::rest
              end
            | _ => raise FatalError "Malformed array access"

      and parse_arrow () = 
          let
            val _ =
                case !stack
                 of (Exp(_),_)::_ => ()
                  | _ => parse_error ("'->' missing left expression",
                                      cur_range ())
            val _ = get_next_token () (* Clear ARROW *)
            val _ = parse_ident "'->' missing name on right side"
          in
            reduce_arrow ()
          end

      and reduce_arrow () =
          case !stack
           of (SymIdent(fname), fnamepos)::(Exp(sp), sppos)::rest =>
              let
                val range = (#1 sppos, #2 fnamepos)
                val deref = A.OpExp (A.DEREF, [sp])
                val exp = mark (A.Select(deref, fname), range)
              in
                stack := (Exp(exp), range)::rest
              end
            | _ => raise FatalError "Malformed arrow expression"
                         
      and parse_dot () = 
          let
            val _ =
                case !stack
                 of (Exp(_),_)::_ => ()
                  | _ => parse_error ("'.' missing left expression",
                                      cur_range ())
            val _ = get_next_token () (* Clear DOT *)
            val _ = parse_ident "'.' missing name on right side"
          in
            reduce_dot ()
          end
      and reduce_dot () =
          case !stack
           of (SymIdent(fname), fnamepos)::(Exp(s), spos)::rest =>
              let
                val range = (#1 spos, #2 fnamepos)
                val exp = mark (A.Select(s, fname), range)
              in
                stack := (Exp(exp), range)::rest
              end
            | _ => raise FatalError "Malformed dot expression"

      and parse_ternary () = 
          let
            val _ = case !stack
                     of (Exp(_),_)::_ => ()
                      | _ => parse_error ("ternary operator missing condition "
                                          ^ "expression", cur_range ())
            val _ = shift () (* QUESTIONMARK *)
            val _ = parse_exp ()
            val _ = if #1 (!next) = COLON then
                      shift ()
                    else 
                      parse_error ("Ternary operator missing ':'", cur_range ())
            val _ = parse_exp ()
          in
            reduce_ternary ()
          end

      and reduce_ternary () =
          case !stack 
           of (Exp(e3),e3pos)::
              (T(COLON,_,_),_)::
              (Exp(e2),_)::
              (T(QUESTIONMARK,_,_),_)::
              (Exp(e1), e1pos)::
              rest =>
              let
                val range = (#1 e1pos, #2 e3pos)
                val tern = mark (A.OpExp(A.COND, [e1, e2, e3]), range)
              in
                stack := (Exp(tern), range)::rest
              end
            | _ => raise FatalError "Reduce ternary"

      and parse_alloc_array () = 
          let
            val _ = get_next_token () (* ALLOC_ARRAY *)
            val _ = demand (LPAREN, "alloc_array missing '('")
            val _ = if parse_type () then
                      ()
                    else
                      parse_error ("Bad type in array allocation", cur_range ())
            val _ = demand (COMMA, "alloc_array missing ','")
            val _ = parse_exp ()
            val _ = demand (RPAREN, "alloc_array missing ')'")
          in
            reduce_alloc_array ()
          end

      and reduce_alloc_array () =
          case !stack
           of (Exp(e),epos)::(Type(tau), tpos)::rest =>
              let
                val range = (#1 tpos, #2 epos)
                val exp = mark (A.AllocArray(tau, e), range)
              in
                stack := (Exp(exp), range)::rest
              end
            | _ => raise FatalError "Malformed array alloc"

      and parse_alloc () = 
          let
            val _ = get_next_token () (* ALLOC *)
            val _ = demand (LPAREN, "Alloc missing '('")
            val _ = if parse_type () then
                      ()
                    else
                      parse_error ("Bad type in alloc", cur_range ())
            val _ = demand (RPAREN, "Alloc missing ')'")
          in
            reduce_alloc ()
          end

      and reduce_alloc () = 
          case !stack
           of (Type(tau), taupos)::rest =>
              stack := (Exp(mark (A.Alloc(tau), taupos)), taupos)::rest
            | _ => raise FatalError "Malformed alloc"
                         

      and reduce_unary () = raise TODO "unary"

      and parse_loop_body () =
          let
            val _ = parse_annos_force ()
            val _ = parse_statement ()
          in
            case !stack
             of (Stm(annos2, b), bpos)::(Annos(annos1), apos)::rest => ()
(* 
                let
                  val range = (#1 apos, #2 bpos)
                  val stm = A.Seq([], [A.Anno(annos1 @ annos2), b])
                in
                  stack := (Stm(nil, stm), range)::rest
                end
*)
              | _ => 
                raise FatalError "Bad loop body"
          end

      and parse_body () = 
          let
            val l_err = "Missing '{' at the beginning of function body"
            val (tok, lpos, _) = !next
            val _ = if tok = LBRACE then shift () else parse_error (l_err, lpos)
            (* val _ = parse_decls () *)
            val _ = parse_statements ()
            val r_err = "Missing '}' at the end of function body"
            val rpos = demand (RBRACE, r_err)
          in
            reduce_body ()
          end

      and parse_fun needs_type = 
          let
            val _ = if needs_type then ( 
                      if parse_type () then 
			()
                      else
			parse_error ("Bad return type in function declaration",
                                     cur_range ()) )
                    else
                      ()

            val _ = parse_fname ()
            val _ = parse_params ()
            val _ = parse_annos_force () (* possibley none *)
	    val _ = 
                case #1 (!next)
                 of SEMI => shift ()
                  | LBRACE => parse_body ()
                  | t => parse_error ("Invalid character " ^ 
                                      (print_term t) ^ 
                                      " following function definition",
                                      cur_range ())
          in
            reduce_fun ()
          end

      and reduce_param () = 
          case !stack
           of (SymIdent(name), npos)::(Type(tau), tpos)::rest =>
              stack := 
              (Param(A.VarDecl(name, tau, NONE, PS.ext (#1 tpos, #2 npos))), 
               (#1 tpos, #2 npos)) :: rest
            | _ => parse_error ("Bad parameter", (cur_range()))

      and reduce_params () = 
          case !stack
           of (Params(plist), listpos)::(Param(p), ppos)::rest =>
              (stack := (Params(p::plist), (#1 ppos, #2 listpos))::rest;
               reduce_params ())
            | (Param(p), ppos)::rest =>
              (stack := (Params([p]), ppos)::rest;
               reduce_params ())
            | (Params(_), _)::_ =>
              ()
            | _ =>
              push (Params([]), (cur_range()))

      and reduce_decls () =
          case !stack
           of (Decls(dlist), listpos)::(Decl(d), dpos)::rest =>
              (stack := (Decls(d::dlist), (#1 dpos, #2 listpos))::rest;
               reduce_decls())
            | (Decl(d), dpos)::rest =>
              (stack := (Decls([d]), (dpos))::rest;
               reduce_decls())
            | (Decls(_), _)::_ => 
              ()
            | _ => 
              push (Decls([]), (cur_pos (), cur_pos()))

      and reduce_statements () =
          case !stack
           of (Stm(annos, A.StmDecl(d)), dpos)::rest =>
	      (stack := (Stms([A.Anno(annos),A.Seq([d], [])]), dpos)::rest; 
               reduce_statements ())
	    | (Stm(annos, s), spos)::rest =>
	      (stack := (Stms([A.Anno(annos), marks (s, spos)]), spos)::rest;
               reduce_statements ())
            | (Stms([A.Seq(ds,ss)]), spos)::(Stm(annos, A.StmDecl(d)), dpos)::rest =>
	      (stack := (Stms([A.Anno(annos), A.Seq(d::ds,ss)]), (#1 dpos, #2 spos))::rest; 
               reduce_statements ())
            | (Stms(ss), sspos)::(Stm(annos, A.StmDecl(d)), dpos)::rest =>
	      (stack := (Stms([A.Anno(annos), A.Seq([d], ss)]), (#1 dpos, #2 sspos))::rest; 
               reduce_statements ())
            | (Stms(ss), sspos)::(Stm(annos, s), spos)::rest => (* s not a decl *)
	      (stack := (Stms(A.Anno(annos)::marks(s, spos)::ss), (#1 spos, #2 sspos))::rest; 
               reduce_statements ())
            | (Stms(ss), sspos)::rest => ()
            | rest => push (Stms([]), cur_range())

      and reduce_body () =
          (print_stack ("reduce_body:");
           case !stack
	    of (Stms(ss), spos)::(Annos(annos), apos)::rest =>
	       ( stack := (Stms(A.Anno(annos)::ss), (#1 apos, #2 spos))::rest ;
		 reduce_body () )
	     | (Stms([A.Seq(ds,ss)]), spos)::(T(LBRACE,_,_),_)::rest =>
	       stack := (Stm(nil,A.Seq(ds,ss)), spos)::rest
             | (Stms(ss), spos)::(T(LBRACE,_,_),_)::rest =>
	       stack := (Stm(nil,A.Seq([],ss)), spos)::rest
             | _ => parse_error ("Invalid body in reduce", cur_range()) (* ?? *)
          )

      and reduce_fun () = 
          (case !stack 
            of [(Stm(nil,s), spos),
                (Annos(a), apos),
                (Params(ps), _),
                (SymIdent(name), _),
                (Type(t), tpos)] => 
               let
                 val range = (#1 tpos, #2 spos)
                 val ext = PS.ext range
                 val f = A.Function(name, t, ps, SOME(s), a, false, ext)
               in
                 stack := [(Gdecl(f), range)]
               end
             | [(T(SEMI,_,_), semipos),
                (Annos(a), apos),
                (Params(ps), _),
                (SymIdent(name), _),
                (Type(t), tpos)] => 
               let
                 val range = (#1 tpos, #2 semipos)
                 val ext = PS.ext range
                 val f = A.Function(name, t, ps, NONE, a, false, ext)
               in
                 stack := [(Gdecl(f), range)]
               end

             | _ => raise FatalError "Malformed function"
          )

      and parse_gdecl () = 
          let
            val (next_tok, startpos, _) = !next
            val _ = 
                case next_tok
                 of STRUCT => parse_struct ()
                  | TYPEDEF => parse_typedef ()
	          | PRAGMA => parse_pragma ()
                  | _ => parse_fun true
          in
            case !stack 
             of [(Gdecl(v), _)] => (stack := []; v)
              | _ => parse_error ("Bad gdecl", startpos)
          end

    in
       {parse_gdecl = parse_gdecl, 
        parse_stm = parse_standalone_statement,
        next = next}
    end

fun parse' filename process_library process_file instream = 
    let
      val _ = PS.pushfile filename (* start at position 0 in filename *)
      val lexer = C0Lex.makeLexer (fn _ => TextIO.input instream)
      val {parse_gdecl, next, ...} = master_parse filename lexer false
      val ast : A.program ref = ref []
      fun process_tokens () =
          let
            val next_gdecl = parse_gdecl()
            val _ = if !ErrorMsg.anyErrors then raise ErrorMsg.Error else ()
	    val _ = case next_gdecl
		     of A.TypeDef(id, tau, ext) => Typetab.bind(id, (tau,ext))
                      | _ => ()
            (* the #use pragma will call the parser recursively *)
	    (* needs to be processed right here *)
	    val next_gdecl' = 
                case next_gdecl
		 of A.Pragma(A.UseLib(libname, NONE), ext) =>
		    A.Pragma(A.UseLib(libname, SOME(process_library libname)),
                             ext)
		  | A.Pragma(A.UseFile(usefile, NONE), ext) =>
		    A.Pragma(A.UseFile(usefile, 
                                       SOME(process_file filename usefile)), 
                             ext)
		  | _ => next_gdecl
            val _ = ast := !ast @ [next_gdecl']
          in
            case !next 
             of (EOF, _, _) => !ast
              | _ => process_tokens ()
          end
    in
      process_tokens () before PS.popfile()
    end
    handle FatalError(s) => (print ("Error: " ^ s ^ "\n"); raise FatalError(s))
         | TODO(s) => (print ("TODO: " ^ s ^ "\n"); raise TODO(s))

fun parse filename process_library process_file = 
    SafeIO.withOpenIn filename (parse' filename process_library process_file)
    handle e as IO.Io _ => ( ErrorMsg.error NONE (exnMessage e) ;
			      raise ErrorMsg.Error )

fun parse_stm filename terminals = 
    let 
      val terminals = ref terminals
      val last_fed : lexresult option ref = ref NONE
      fun lexer () = 
          case !terminals of 
            [] => (last_fed := NONE; (EOF, (0,0), NONE))
          | (term :: terms) =>
            (last_fed := SOME term; terminals := terms; term)
      val {parse_stm, ...} = master_parse filename lexer true
      fun get_unused () =
          case !last_fed of
            NONE => !terminals
          | SOME term => term :: !terminals
      val (annos, stm, pos) = parse_stm ()
    in
      SOME (get_unused (), annos, stm, pos) 
    end
    handle DemandEOF => NONE
end
