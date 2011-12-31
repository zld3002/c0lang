(* C0 Compiler
 * Lexer
 * Author: Frank Pfenning <fp@cs.cmu.edu>
 *)

structure A = Ast
structure S = Symbol
structure T = Typetab
structure PS = ParseState

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) Tokens.token

local
  val commentLevel = ref 0	(* for lexing delimited comments *)
  val commentPos = ref 0	(* for lexing delimited comments *)
  val inCommentLine = ref false (* for lexing single-line comments *)
  val inAnno = ref false        (* for lexing delimited annotations *)
  val annoPos = ref 0		(* for lexing delimited annotations *)
  val inAnnoLine = ref false    (* for lexing single-line annotations *)
  val stringStart = ref 0	(* for lexing strings *)
  val stringList : string list ref = ref nil (* for lexing strings *)
  val pragmaString = ref ""     (* for lexing pragmas *)
  val inPragma = ref false      (* for lexing pragmas, which are single-line *)
in
  fun enterComment yypos =
      ( commentLevel := !commentLevel + 1 ;
	commentPos := yypos )
    
  fun exitComment () =
      ( commentLevel := !commentLevel - 1 ;
	!commentLevel = 0 )

  fun enterCommentLine () =
      ( inCommentLine := true )

  fun exitCommentLine () =
      ( inCommentLine := false )

  (* lexing annotations *)
  fun enterAnno (yytext, yypos) =
      if !inAnno
      then ( ErrorMsg.error (PS.ext (yypos, yypos+size yytext))
			    ("no nested annotations permitted") ; () )
      else ( inAnno := true ; annoPos := yypos ; () )

  fun exitAnno (yytext, yypos) =
      if !inAnno
      then ( inAnno := false ; () )
      else ( ErrorMsg.error (PS.ext (yypos, yypos+size yytext))
			    ("token `@*/' outside annotation") ; () )

  fun enterAnnoLine (yytext, yypos) =
      if !inAnnoLine
      then ( ErrorMsg.error (PS.ext (yypos, yypos+size yytext))
			    ("no nested annotations permitted") ; () )
      else ( inAnnoLine := true ; () )

  fun annoNewLine () =
      if !inAnnoLine
      then ( inAnnoLine := false; true )
      else false

  fun newLineInComment (yypos) =
      if !inAnnoLine
      then ( ErrorMsg.error (PS.ext (yypos, yypos+1))
			    ("end of delimited comment in single-line annotation") ;
	     inAnnoLine := false ;
	     () )
      else ()

  fun atChars (yytext, yypos) =
      if !inAnno orelse !inAnnoLine
      then ()
      else ( ErrorMsg.error (PS.ext (yypos, yypos+size yytext))
			    ("using character `@' outside annotations") ; () )
  (* end annotations *)

  fun number (yytext, yypos) fromString numType =
      let
        val ext = PS.ext (yypos, yypos + size yytext)
	val numOpt = fromString yytext
		     handle Overflow =>
			    ( ErrorMsg.error ext
			        ("integral " ^ numType ^ " constant `" ^ yytext ^ "' too large") ;
			      NONE )
      in 
	  case numOpt
	   of NONE => ( ErrorMsg.error ext
			  ("cannot parse integral " ^ numType ^ " constant `" ^ yytext ^ "'") ;
			Tokens.INTCONST (Word32Signed.ZERO, yypos, yypos + size yytext) )
            | SOME(n) => Tokens.INTCONST(n, yypos, yypos + size yytext)
      end

  fun hexNumber (yytext, yypos) = number (yytext, yypos) Word32Signed.fromHexString "hexadecimal"
  fun decNumber (yytext, yypos) = number (yytext, yypos) Word32Signed.fromString "decimal"

  fun eof () = 
      ( if !commentLevel > 0
        then ( ErrorMsg.error (PS.ext (!commentPos,!commentPos)) "comment not terminated" ;
	       commentLevel := 0 )
        else () ;
        if !inCommentLine
	then ( ErrorMsg.error NONE "single line comment not terminated by newline at end of file" ;
	       inCommentLine := false )
	else () ;
	if !inAnno
	then ( ErrorMsg.error (PS.ext (!annoPos,!annoPos)) "delimited annotation not terminated" ;
	       inAnno := false )
	else () ;
	if !inAnnoLine
	then ( ErrorMsg.error NONE "single-line annotation at end of file not terminated with newline" ;
	       inAnnoLine := false )
	else () ;
	if !inPragma
	then ( ErrorMsg.error NONE "compiler directive at end of file not terminated with newline" ;
	       inPragma := false )
	else () ;
	Tokens.EOF(0,0) )		(* bogus position information; unused *)

  fun ident (id, yytext, yypos) =
      (case Typetab.lookup (id)
         of NONE => Tokens.IDENT(id, yypos, yypos + size yytext)
          | SOME _ => Tokens.TYPENAME(id, yypos, yypos + size yytext))

  fun convertChar (yytext, yypos) =
      let
	val ext = PS.ext (yypos, yypos+size yytext)
	fun checkValid (NONE) =
	      ( ErrorMsg.error ext ("character constant " ^ yytext ^ " malformed") ; #"?" )
	  | checkValid (SOME(c)) = c
	val stripped = String.substring(yytext, 1, size yytext - 2)
      in
	  Tokens.CHARCONST(checkValid(C0Char.fromC0String(stripped)), yypos, yypos+size yytext)
      end

  fun initString (yypos) =
      ( stringStart := yypos ;
	stringList := nil ;
        () )

  fun addString (yytext) =
      ( stringList := yytext::(!stringList) ; () )

  fun addCharString (NONE, yytext, yypos) =
      ( ErrorMsg.error (PS.ext (yypos, yypos+size yytext))
          ("ignoring illegal escape sequence `" ^ yytext ^ "' not legal in strings") ;
	() )
    | addCharString (SOME(c), yytext, yypos) = addString (String.str(c))

  fun addSpecialChar (yytext as "\\0", yypos) =
      ( ErrorMsg.error (PS.ext (yypos, yypos + size yytext))
	  ("ignoring illegal null escape sequence: `" ^ yytext ^ "' not legal in strings") ;
	() )
    | addSpecialChar (yytext, yypos) =
        addCharString (C0Char.fromC0String yytext, yytext, yypos)

  fun convertString (yypos) = (* yypos is position of closing double-quote *)
      let
	  val str = String.concat (List.rev (!stringList))
      in
	  Tokens.STRINGCONST(str, !stringStart, yypos+1)
      end

  fun initPragma (yytext, yypos) = (* yytext is "#{id}" *)
      ( initString(yypos) ;
	pragmaString := yytext ;
	inPragma := true ;
	() )

  fun convertPragma (yypos) = (* yypos is the position of closing newline *)
      let
	 val pragmaLine = String.concat (List.rev (!stringList))
	 val _ = ( inPragma := false )
      in
         Tokens.PRAGMA((!pragmaString, pragmaLine), !stringStart, yypos+1)
      end

end

%%
%header (functor C0LexFn(structure Tokens : C0_TOKENS));
%full
%s STRING COMMENT COMMENT_LINE PRAGMA;

id = [A-Za-z_][A-Za-z0-9_]*;
decnum = (0|[1-9][0-9]*);
hexdigit = [0-9a-fA-F];
hexnum = 0[xX]{hexdigit}+;
string = \".*\";
simplechar = '[^\n\\]';
escapechar = '\\.';
ws = [\ \t\011\012\r];

%%

<INITIAL> {ws}+       => (lex ());
<INITIAL> \n          => (PS.newline(yypos);
			  if annoNewLine()
			  then Tokens.ANNO_END (yypos, yypos+1)
			  else lex());

<INITIAL> "{"         => (Tokens.LBRACE (yypos, yypos + size yytext));
<INITIAL> "}"         => (Tokens.RBRACE (yypos, yypos + size yytext));
<INITIAL> "("         => (Tokens.LPAREN (yypos, yypos + size yytext));
<INITIAL> ")"         => (Tokens.RPAREN (yypos, yypos + size yytext));
<INITIAL> "["         => (Tokens.LBRACKET (yypos, yypos + size yytext));
<INITIAL> "]"         => (Tokens.RBRACKET (yypos, yypos + size yytext));

<INITIAL> ","         => (Tokens.COMMA (yypos, yypos + size yytext));
<INITIAL> ":"         => (Tokens.COLON (yypos, yypos + size yytext));
<INITIAL> ";"         => (Tokens.SEMI (yypos, yypos + size yytext));
<INITIAL> "."         => (Tokens.DOT (yypos, yypos + size yytext));

<INITIAL> "="         => (Tokens.EQ (yypos, yypos + size yytext));
<INITIAL> "+="        => (Tokens.PLUSEQ (yypos, yypos + size yytext));
<INITIAL> "-="        => (Tokens.MINUSEQ (yypos, yypos + size yytext));
<INITIAL> "*="        => (Tokens.STAREQ (yypos, yypos + size yytext));
<INITIAL> "/="        => (Tokens.SLASHEQ (yypos, yypos + size yytext));
<INITIAL> "%="        => (Tokens.PERCENTEQ (yypos, yypos + size yytext));
<INITIAL> "&="        => (Tokens.AMPEQ (yypos, yypos + size yytext));
<INITIAL> "^="        => (Tokens.CARETEQ (yypos, yypos + size yytext));
<INITIAL> "|="        => (Tokens.BAREQ (yypos, yypos + size yytext));
<INITIAL> "<<="       => (Tokens.LLEQ (yypos, yypos + size yytext));
<INITIAL> ">>="       => (Tokens.GGEQ (yypos, yypos + size yytext));
<INITIAL> "++"        => (Tokens.PLUSPLUS (yypos, yypos + size yytext));
<INITIAL> "--"        => (Tokens.MINUSMINUS (yypos, yypos + size yytext));

<INITIAL> "+"         => (Tokens.PLUS (yypos, yypos + size yytext));
<INITIAL> "-"         => (Tokens.MINUS (yypos, yypos + size yytext));
<INITIAL> "*"         => (Tokens.STAR (yypos, yypos + size yytext));
<INITIAL> "/"         => (Tokens.SLASH (yypos, yypos + size yytext));
<INITIAL> "%"         => (Tokens.PERCENT (yypos, yypos + size yytext));
<INITIAL> "<"         => (Tokens.LESS (yypos, yypos + size yytext));
<INITIAL> "<="        => (Tokens.LESSEQ (yypos, yypos + size yytext));
<INITIAL> ">"         => (Tokens.GREATER (yypos, yypos + size yytext));
<INITIAL> ">="        => (Tokens.GREATEREQ (yypos, yypos + size yytext));
<INITIAL> "=="        => (Tokens.EQEQ (yypos, yypos + size yytext));
<INITIAL> "!="        => (Tokens.BANGEQ (yypos, yypos + size yytext));
<INITIAL> "&&"        => (Tokens.AMPAMP (yypos, yypos + size yytext));
<INITIAL> "||"        => (Tokens.BARBAR (yypos, yypos + size yytext));
<INITIAL> "&"         => (Tokens.AMP (yypos, yypos + size yytext));
<INITIAL> "^"         => (Tokens.CARET (yypos, yypos + size yytext));
<INITIAL> "|"         => (Tokens.BAR (yypos, yypos + size yytext));
<INITIAL> "<<"        => (Tokens.LL (yypos, yypos + size yytext));
<INITIAL> ">>"        => (Tokens.GG (yypos, yypos + size yytext));
<INITIAL> "!"         => (Tokens.BANG (yypos, yypos + size yytext));
<INITIAL> "~"         => (Tokens.TILDE (yypos, yypos + size yytext));
<INITIAL> "->"        => (Tokens.ARROW (yypos, yypos + size yytext));

<INITIAL> "?"         => (Tokens.QUESTIONMARK (yypos, yypos + size yytext));

<INITIAL> "struct"    => (Tokens.STRUCT (yypos, yypos + size yytext));
<INITIAL> "typedef"   => (Tokens.TYPEDEF (yypos, yypos + size yytext));
<INITIAL> "int"       => (Tokens.INT (yypos, yypos + size yytext));
<INITIAL> "bool"      => (Tokens.BOOL (yypos, yypos + size yytext));
<INITIAL> "char"      => (Tokens.CHAR (yypos, yypos + size yytext));
<INITIAL> "string"    => (Tokens.STRING (yypos, yypos + size yytext));
<INITIAL> "void"      => (Tokens.VOID (yypos, yypos + size yytext));
<INITIAL> "if"        => (Tokens.IF (yypos, yypos + size yytext));
<INITIAL> "else"      => (Tokens.ELSE (yypos, yypos + size yytext));
<INITIAL> "for"       => (Tokens.FOR (yypos, yypos + size yytext));
<INITIAL> "while"     => (Tokens.WHILE (yypos, yypos + size yytext));
<INITIAL> "continue"  => (Tokens.CONTINUE (yypos, yypos + size yytext));
<INITIAL> "break"     => (Tokens.BREAK (yypos, yypos + size yytext));
<INITIAL> "return"    => (Tokens.RETURN (yypos, yypos + size yytext));
<INITIAL> "true"      => (Tokens.TRUE (yypos, yypos + size yytext));
<INITIAL> "false"     => (Tokens.FALSE (yypos, yypos + size yytext));
<INITIAL> "NULL"      => (Tokens.NULL (yypos, yypos + size yytext));
<INITIAL> "alloc"     => (Tokens.ALLOC (yypos, yypos + size yytext));
<INITIAL> "alloc_array" => (Tokens.ALLOC_ARRAY (yypos, yypos + size yytext));

<INITIAL> "\\result"  => (Tokens.BS_RESULT (yypos, yypos + size yytext));
<INITIAL> "\\length"  => (Tokens.BS_LENGTH (yypos, yypos + size yytext));
<INITIAL> "\\old"     => (Tokens.BS_OLD (yypos, yypos + size yytext));
<INITIAL> "requires"  => (Tokens.REQUIRES (yypos, yypos + size yytext));
<INITIAL> "ensures"   => (Tokens.ENSURES (yypos, yypos + size yytext));
<INITIAL> "loop_invariant"  => (Tokens.LOOP_INVARIANT (yypos, yypos + size yytext));
<INITIAL> "assert"    => (Tokens.ASSERT (yypos, yypos + size yytext));

<INITIAL> {decnum}    => (decNumber (yytext, yypos));
<INITIAL> {hexnum}    => (hexNumber (yytext,yypos));
<INITIAL> {id}        => (let
                            val id = Symbol.symbol yytext
                          in 
                            ident (id, yytext, yypos)
                          end);
<INITIAL> {simplechar} => (convertChar(yytext, yypos));
<INITIAL> {escapechar} => (convertChar(yytext, yypos));
<INITIAL> \"          => (YYBEGIN STRING; initString(yypos); lex());
<INITIAL> @           => (atChars(yytext, yypos); lex());
<INITIAL> "/*@"       => (enterAnno(yytext, yypos); Tokens.ANNO_BEGIN (yypos, yypos + size yytext));
<INITIAL> "/*"        => (YYBEGIN COMMENT; enterComment yypos; lex());
<INITIAL> "@*/"       => (exitAnno(yytext, yypos); Tokens.ANNO_END (yypos, yypos + size yytext));
<INITIAL> "*/"        => (ErrorMsg.error (PS.ext (yypos, yypos)) "unbalanced comments";
                          lex());

<INITIAL> "//@"       => (enterAnnoLine(yytext, yypos); Tokens.ANNO_BEGIN (yypos, yypos + size yytext));
<INITIAL> "//"        => (enterCommentLine(); YYBEGIN COMMENT_LINE; lex());
<INITIAL> #{id}       => (YYBEGIN PRAGMA; initPragma(yytext, yypos); lex());
<INITIAL> #           => (YYBEGIN PRAGMA; initPragma(yytext, yypos); lex());
<INITIAL> .           => (ErrorMsg.error (PS.ext (yypos,yypos+1))
		            ("illegal character: \"" ^ yytext ^ "\"");
                          lex ());

<STRING> \"           => (YYBEGIN INITIAL; convertString(yypos));
<STRING> \n           => (ErrorMsg.error (PS.ext (yypos,yypos))
			    ("illegal newline in string; use \\n");
			  PS.newline(yypos);
			  lex());
<STRING> [^"\\\n]*    => (addString(yytext); lex());
<STRING> \\\n         => (PS.newline(yypos); addSpecialChar(yytext,yypos); lex());
<STRING> \\.          => (addSpecialChar(yytext,yypos); lex());
<STRING> .            => (ErrorMsg.error (PS.ext (yypos,yypos+1))
			    ("illegal character in string: `" ^ yytext ^ "'");
			  lex ());

<COMMENT> "/*"        => (enterComment yypos; lex());
<COMMENT> "*/"        => (if exitComment () then YYBEGIN INITIAL else (); lex());
<COMMENT> \n          => (PS.newline(yypos); newLineInComment(yypos); lex ());
<COMMENT> .           => (lex());

<COMMENT_LINE> \n     => (PS.newline(yypos); YYBEGIN INITIAL;
			  if annoNewLine()
			  then (exitCommentLine(); Tokens.ANNO_END(yypos, yypos+1))
			  else (exitCommentLine(); lex()));
<COMMENT_LINE> .      => (lex());

<PRAGMA> \n           => (PS.newline(yypos); YYBEGIN INITIAL; convertPragma(yypos));
<PRAGMA> [^\\\n]*     => (addString(yytext); lex());
<PRAGMA> \\\n         => (PS.newline(yypos); addString(yytext); lex());
<PRAGMA> \\.          => (addString(yytext); lex());
