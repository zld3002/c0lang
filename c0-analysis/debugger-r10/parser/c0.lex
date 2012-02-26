type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) Tokens.token

local
  val commentLevel = ref 0	(* for lexing comments *)
  val commentPos = ref 0	(* for lexing comments *)
  val stringStart = ref 0	(* for lexing strings *)
  val stringList : string list ref = ref nil (* for lexing strings *)
in
  val typeName = ref ""
  val return_to = ref "INITIAL"

  fun enterComment yypos =
      ( commentLevel := !commentLevel + 1 ;
	commentPos := yypos )
    
  fun exitComment () =
      ( commentLevel := !commentLevel - 1 ;
	!commentLevel = 0 )

  fun ident yyt yyp = 
      if ParseState.istype yyt
      then Tokens.TYPE_IDENT (yyt, yyp, yyp + size yyt)
      else Tokens.IDENT (yyt, yyp, yyp + size yyt)

  fun number (yyt, yyp) fromString numType =
      let
        val ext = ParseState.ext (yyp, yyp + size yyt)
	val numOpt = fromString yyt
		     handle Overflow =>
			    ( ErrorMsg.error ext
			        ("integral " ^ numType ^ " constant `" ^ yyt ^ "' too large") ;
			      NONE )
      in 
	  case numOpt
	   of NONE => ( ErrorMsg.error ext
			  ("cannot parse integral " ^ numType ^ " constant `" ^ yyt ^ "'") ;
			Tokens.INTCONST (Word32Signed.ZERO, yyp, yyp + size yyt) )
            | SOME(n) => Tokens.INTCONST(n, yyp, yyp + size yyt)
      end

  fun hexNumber (yyt, yyp) = number (yyt, yyp) Word32Signed.fromHexString "hexadecimal"
  fun decNumber (yyt, yyp) = number (yyt, yyp) Word32Signed.fromString "decimal"

  fun convertChar (yyt, yyp) =
      let
	val ext = ParseState.ext (yyp, yyp+size yyt)
	fun checkValid (NONE) =
	      ( ErrorMsg.error ext ("character constant " ^ yyt ^ " malformed") ; #"?" )
	  | checkValid (SOME(#"\000")) =
	      ( ErrorMsg.error ext ("null character constant " ^ yyt ^ " not allowed") ; #"?" )
	  | checkValid (SOME(c)) = c
	val stripped = String.substring(yyt, 1, size yyt - 2)
      in
	  Tokens.CHARCONST(checkValid(Char.fromCString(stripped)), yyp, yyp+size yyt)
      end

  fun initString (yyp) =
      ( stringStart := yyp;
	stringList := nil ;
        ()
      )

  fun addString (yyt) =
      ( stringList := yyt::(!stringList) ; () )

  fun addCharString (NONE, yyt, yyp) =
      ( ErrorMsg.error (ParseState.ext (yyp, yyp+size yyt))
		       ("ignoring illegal escape sequence `" ^ yyt ^ "' not legal in strings") ;
	() )
    | addCharString (SOME(c), yyt, yyp) = addString (String.str(c))

  fun addSpecialChar (yyt as "\\0", yyp) =
      ( ErrorMsg.error (ParseState.ext (yyp, yyp + size yyt))
	  ("ignoring illegal null escape sequence: `" ^ yyt ^ "' not legal in strings") ;
	() )
    | addSpecialChar (yyt, yyp) =
        addCharString (Char.fromCString yyt, yyt, yyp)

  fun convertString (yyp) = (* yyp is position of closing double-quote *)
      let
	  val str = String.concat (List.rev (!stringList))
      in
	  Tokens.STRINGCONST(str, !stringStart, yyp+1)
      end

  fun eof () =  
      ( if (!commentLevel > 0)
          then (ErrorMsg.error (ParseState.ext (!commentPos,!commentPos)) "unterminated comment")
          else ();
	Tokens.EOF (0,0) )
end

%%
%header (functor C0LexFn(structure Tokens : C0_TOKENS));
%full
%s TYPEDEF STRING COMMENT COMMENT_LINE ANNOT ANNOT_LINE;

id = [A-Za-z_][A-Za-z0-9_]*;
decnum = (0|[1-9][0-9]*);
hexdigit = [0-9a-fA-F];
hexnum = 0[xX]{hexdigit}+;
string = \".*\";
simplechar = '[^\n\\]';
escapechar = '\\.';
ws = [\ \t\012\r];

%%

<INITIAL> {ws}+       => (lex ());
<INITIAL> \n          => (ParseState.newline(yypos); lex());

<INITIAL> "{"         => (Tokens.LBRACE (yypos, yypos + size yytext));
<INITIAL> "}"         => (Tokens.RBRACE (yypos, yypos + size yytext));
<INITIAL> "("         => (Tokens.LPAREN (yypos, yypos + size yytext));
<INITIAL> ")"         => (Tokens.RPAREN (yypos, yypos + size yytext));
<INITIAL> "["         => (Tokens.LBRACK (yypos, yypos + size yytext));
<INITIAL> "]"         => (Tokens.RBRACK (yypos, yypos + size yytext));

<INITIAL> ";"         => (Tokens.SEMI (yypos, yypos + size yytext));

<INITIAL> "=="        => (Tokens.EQEQ (yypos, yypos + size yytext));
<INITIAL> "="         => (Tokens.EQ (yypos, yypos + size yytext));
<INITIAL> "+="        => (Tokens.PLUSEQ (yypos, yypos + size yytext));
<INITIAL> "->"        => (Tokens.ARROW (yypos, yypos + size yytext));
<INITIAL> "-="        => (Tokens.MINUSEQ (yypos, yypos + size yytext));
<INITIAL> "*="        => (Tokens.STAREQ (yypos, yypos + size yytext));
<INITIAL> "/="        => (Tokens.SLASHEQ (yypos, yypos + size yytext));
<INITIAL> "%="        => (Tokens.PERCENTEQ (yypos, yypos + size yytext));
<INITIAL> "&="        => (Tokens.AMPEREQ (yypos, yypos + size yytext));
<INITIAL> "^="        => (Tokens.CAROTEQ (yypos, yypos + size yytext));
<INITIAL> "|="        => (Tokens.BAREQ (yypos, yypos + size yytext));
<INITIAL> "<<="       => (Tokens.LTLTEQ (yypos, yypos + size yytext));
<INITIAL> ">>="       => (Tokens.GTGTEQ (yypos, yypos + size yytext));
<INITIAL> "&&="       => (Tokens.AMPERAMPEREQ (yypos, yypos + size yytext));
<INITIAL> "||="       => (Tokens.BARBAREQ (yypos, yypos + size yytext));
<INITIAL> "<<"       => (Tokens.LTLT (yypos, yypos + size yytext));
<INITIAL> ">>"       => (Tokens.GTGT (yypos, yypos + size yytext));

<INITIAL> "+"         => (Tokens.PLUS (yypos, yypos + size yytext));
<INITIAL> "++"        => (Tokens.PLUSPLUS (yypos, yypos + size yytext));
<INITIAL> "-"         => (Tokens.MINUS (yypos, yypos + size yytext));
<INITIAL> "--"        => (Tokens.MINUSMINUS (yypos, yypos + size yytext));
<INITIAL> "*"         => (Tokens.STAR (yypos, yypos + size yytext));
<INITIAL> "/"         => (Tokens.SLASH (yypos, yypos + size yytext));
<INITIAL> "%"         => (Tokens.PERCENT (yypos, yypos + size yytext));
<INITIAL> "<="         => (Tokens.LTEQ (yypos, yypos + size yytext));
<INITIAL> "<"         => (Tokens.LT (yypos, yypos + size yytext));
<INITIAL> ">="         => (Tokens.GTEQ (yypos, yypos + size yytext));
<INITIAL> ">"         => (Tokens.GT (yypos, yypos + size yytext));
<INITIAL> "!="         => (Tokens.BANGEQ (yypos, yypos + size yytext));
<INITIAL> "&&"         => (Tokens.AMPERAMPER (yypos, yypos + size yytext));
<INITIAL> "||"         => (Tokens.BARBAR (yypos, yypos + size yytext));
<INITIAL> "&"         => (Tokens.AMPER (yypos, yypos + size yytext));
<INITIAL> "|"         => (Tokens.BAR (yypos, yypos + size yytext));
<INITIAL> "^"         => (Tokens.CAROT (yypos, yypos + size yytext));
<INITIAL> "!"         => (Tokens.BANG (yypos, yypos + size yytext));
<INITIAL> "~"         => (Tokens.TILDE (yypos, yypos + size yytext));
<INITIAL> ":"         => (Tokens.COLON (yypos, yypos + size yytext));
<INITIAL> ","         => (Tokens.COMMA (yypos, yypos + size yytext));
<INITIAL> "?"         => (Tokens.QMARK (yypos, yypos + size yytext));
<INITIAL> "."         => (Tokens.PERIOD (yypos, yypos + size yytext));

<INITIAL> "return"    => (Tokens.RETURN (yypos, yypos + size yytext));
<INITIAL> "if"        => (Tokens.IF (yypos, yypos + size yytext));
<INITIAL> "else"      => (Tokens.ELSE (yypos, yypos + size yytext));
<INITIAL> "while"     => (Tokens.WHILE (yypos, yypos + size yytext));
<INITIAL> "for"       => (Tokens.FOR (yypos, yypos + size yytext));
<INITIAL> "continue"  => (Tokens.CONTINUE (yypos, yypos + size yytext));
<INITIAL> "break"     => (Tokens.BREAK (yypos, yypos + size yytext));
<INITIAL> "struct"    => (Tokens.STRUCT (yypos, yypos + size yytext));
<INITIAL> "true"      => (Tokens.TRUE (yypos, yypos + size yytext));
<INITIAL> "false"     => (Tokens.FALSE (yypos, yypos + size yytext));
<INITIAL> "NULL"      => (Tokens.NULL (yypos, yypos + size yytext));
<INITIAL> "alloc"       => (Tokens.ALLOC (yypos, yypos + size yytext));
<INITIAL> "alloc_array" => (Tokens.ALLOCARRAY (yypos, yypos + size yytext));
<INITIAL> "typedef"    => (YYBEGIN TYPEDEF; Tokens.TYPEDEF (yypos, yypos + size yytext));

<INITIAL> "void"     => (Tokens.VOID (yypos, yypos + size yytext));
<INITIAL> "bool"     => (Tokens.BOOL (yypos, yypos + size yytext));
<INITIAL> "int"      => (Tokens.INT (yypos, yypos + size yytext));
<INITIAL> "string"      => (Tokens.STRING (yypos, yypos + size yytext));
<INITIAL> "char"      => (Tokens.CHAR (yypos, yypos + size yytext));

<INITIAL> {decnum}    => (decNumber (yytext, yypos));
<INITIAL> {hexnum}    => (hexNumber (yytext,yypos));

<INITIAL> {simplechar} => (convertChar(yytext, yypos));
<INITIAL> {escapechar} => (convertChar(yytext, yypos));

<INITIAL> {id}        => (ident yytext yypos);

<INITIAL> "/*"        => (return_to := "INITIAL"; YYBEGIN COMMENT; enterComment yypos; lex());
<INITIAL> "*/"        => (ErrorMsg.error (ParseState.ext (yypos, yypos)) "unbalanced comments";
                          lex());

<INITIAL> "//"        => (return_to := "INITIAL"; YYBEGIN COMMENT_LINE; lex());
<INITIAL> "#"         => (return_to := "INITIAL"; YYBEGIN COMMENT_LINE; lex());
<INITIAL> "\""        => (YYBEGIN STRING; initString(yypos); lex());

<INITIAL> "/*@"       => (lex());
<INITIAL> "@*/"        => (lex());
<INITIAL> "//@"       => (lex());

<INITIAL> .           => (ErrorMsg.error (ParseState.ext (yypos,yypos))
                              ("illegal character: \"" ^ yytext ^ "\"");
                          lex ());

<TYPEDEF> {ws}+       => (lex ());
<TYPEDEF> \n          => (ParseState.newline(yypos); lex());

<TYPEDEF> "struct"    => (Tokens.STRUCT (yypos, yypos + size yytext));
<TYPEDEF> "void"     => (Tokens.VOID (yypos, yypos + size yytext));
<TYPEDEF> "bool"     => (Tokens.BOOL (yypos, yypos + size yytext));
<TYPEDEF> "int"      => (Tokens.INT (yypos, yypos + size yytext));
<TYPEDEF> "string"      => (Tokens.STRING (yypos, yypos + size yytext));
<TYPEDEF> "char"      => (Tokens.CHAR (yypos, yypos + size yytext));
<TYPEDEF> "["         => (Tokens.LBRACK (yypos, yypos + size yytext));
<TYPEDEF> "]"         => (Tokens.RBRACK (yypos, yypos + size yytext));
<TYPEDEF> "*"         => (Tokens.STAR (yypos, yypos + size yytext));
<TYPEDEF> ";"         => (YYBEGIN INITIAL before ParseState.newtype (!typeName);
			  Tokens.SEMI (yypos, yypos + size yytext));
<TYPEDEF> {id}        => (typeName := yytext; ident yytext yypos);

<TYPEDEF> "/*"        => (return_to := "TYPEDEF"; YYBEGIN COMMENT; enterComment yypos; lex());
<TYPEDEF> "*/"        => (ErrorMsg.error (ParseState.ext (yypos, yypos)) "unbalanced comments";
                          lex());

<TYPEDEF> "//"        => (return_to := "TYPEDEF"; YYBEGIN COMMENT_LINE; lex());
<TYPEDEF> "#"         => (return_to := "TYPEDEF"; YYBEGIN COMMENT_LINE; lex());

<TYPEDEF> .           => (ErrorMsg.error (ParseState.ext (yypos,yypos))
                              ("illegal character: \"" ^ yytext ^ "\"");
                          lex ());

<COMMENT> "/*"        => (enterComment yypos; lex());
<COMMENT> "*/"        => (if exitComment () 
			  then (case !return_to
				 of "INITIAL" => YYBEGIN INITIAL
				  | "TYPEDEF" => YYBEGIN TYPEDEF
				  | "ANNOT" => YYBEGIN ANNOT
				  | "ANNOT_LINE" => YYBEGIN ANNOT_LINE
				  | _ => raise Match
				)
			  else (); lex());
<COMMENT> \n          => (ParseState.newline(yypos); lex ());
<COMMENT> .           => (lex());

<COMMENT_LINE> \n     => (ParseState.newline(yypos); 
			  (case !return_to
				 of "INITIAL" => YYBEGIN INITIAL
				  | "TYPEDEF" => YYBEGIN TYPEDEF
				  | "ANNOT" => YYBEGIN ANNOT
				  | "ANNOT_LINE" => YYBEGIN ANNOT_LINE
				  | _ => raise Match
				); lex());
<COMMENT_LINE> .      => (lex());

<STRING> \"           => (YYBEGIN INITIAL; convertString(yypos));
<STRING> \n           => (ErrorMsg.error (ParseState.ext (yypos,yypos))
			    ("illegal newline in string; use \\n");
			  ParseState.newline(yypos);
			  lex());
<STRING> [^"\\\n]*    => (addString(yytext); lex());
<STRING> \\\n         => (addSpecialChar(yytext,yypos); lex());
<STRING> \\.          => (addSpecialChar(yytext,yypos); lex());
<STRING> .            => (ErrorMsg.error (ParseState.ext (yypos,yypos))
			    ("illegal character in string: `" ^ yytext ^ "'");
			  lex ());
