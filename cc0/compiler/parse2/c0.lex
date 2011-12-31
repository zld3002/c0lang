(* C0 Compiler
 * Lexer
 * Author: Frank Pfenning <fp@cs.cmu.edu>
 *)

structure A = Ast
structure S = Symbol
structure T = Typetab
structure PS = ParseState

(* This type defines all the different types of tokens in the language *)
datatype terminal =
  PRAGMA | BS_OLD | BS_LENGTH | BS_RESULT| ASSERT | LOOP_INVARIANT | ENSURES
| REQUIRES | ANNO_END | ANNO_BEGIN | RBRACKET | LBRACKET | RPAREN 
| LPAREN | RBRACE | LBRACE | MINUSMINUS | PLUSPLUS | GGEQ | LLEQ | BAREQ 
| CARETEQ | AMPEQ | PERCENTEQ | SLASHEQ | STAREQ | MINUSEQ | PLUSEQ | EQ | ARROW
| DOT | TILDE | BANG | GG | LL | BAR | CARET | AMP | BARBAR | AMPAMP | BANGEQ
| EQEQ | GREATEREQ | GREATER | LESSEQ | LESS | PERCENT | SLASH | STAR | MINUS
| PLUS | ALLOC_ARRAY | ALLOC | NULL | FALSE | TRUE | RETURN | BREAK | CONTINUE
| FOR | WHILE | ELSE | IF | VOID | CHAR | STRING_TAU | BOOL | INT | TYPEDEF 
| STRUCT | CHARCONST | STRINGCONST | TYPENAME | IDENT | VARNAME
| DECCONST | HEXCONST | QUESTIONMARK | SEMI | COLON | COMMA | EOF


(* A token consists of the token type, the start and end positions of the
   token, and possibly a string value (for things like idents or intconsts).
   Intconst strings are converted to ints in the parser, rather than lexer,
   so that I can have a simple, streamlined type here that's easy to pattern
   match on
*)
type lexresult = terminal * (int * int) * string option

(* local *)
  val interactive = ref false	(* the interpreter doesn't want EOF errors *)
  val commentLevel = ref 0	(* for lexing delimited comments *)
  val commentPos = ref 0	(* for lexing delimited comments *)
  val inCommentLine = ref false (* for lexing single-line comments *)
  val inAnno = ref false        (* for lexing delimited annotations *)
  val annoPos = ref 0		(* for lexing delimited annotations *)
  val inAnnoLine = ref false    (* for lexing single-line annotations *)
  val stringStart = ref 0	(* for lexing strings *)
  val stringList : string list ref = ref nil (* for lexing strings *)
  val inPragma = ref false      (* for lexing pragmas, which are single-line *)
(* in *)
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
			    ("using character `@' outside annotations") ; ())
  (* end annotations *)


  fun eof () = 
      if !interactive then (EOF, (0,0), NONE) else ( 
        if !commentLevel > 0
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
	(EOF, (0,0), NONE : string option))		(* bogus position information; unused *)

  fun convertChar (yytext, yypos) =
      let
          val ext = PS.ext (yypos, yypos+size yytext)
	      fun checkValid (NONE) =
	         ( ErrorMsg.error ext ("character constant " ^ yytext ^ " malformed") ; #"?" )
	        | checkValid (SOME(c)) = c
              val stripped = String.substring(yytext, 1, size yytext - 2)
              val _ = checkValid (C0Char.fromC0String(stripped))
      in
	      (CHARCONST, (yypos, yypos + size yytext), SOME(stripped))
      end

  fun initString (yypos) =
      ( stringStart := yypos;
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
	      val result : lexresult = (STRINGCONST, (!stringStart, yypos+1), SOME(str))
      in
	      result
      end

  fun initPragma (yytext, yypos) = (* yytext is "#{id}" *)
      ( initString(yypos) ;
	stringList := [yytext] ;
	inPragma := true ;
	() )

  fun convertPragma (yypos) = (* yypos is the position of closing newline *)
      let
	 val pragmaLine = String.concat (List.rev (!stringList))
	 val _ = ( inPragma := false )
      in
         (PRAGMA, (!stringStart, yypos+1), SOME(pragmaLine))
      end

(* end *) (* local *)

%%
%reject
%structure C0Lex
%full
%s STRING COMMENT COMMENT_LINE PRAGMA;

id = [A-Za-z_][A-Za-z0-9_]*;
decnum = (0|[1-9][0-9]*);
hexdigit = [0-9a-fA-F];
hexnum = 0[xX]{hexdigit}+;
string = \".*\";
simplechar = '[^\n\\]';
escapechar = '\\.';
badchar = ('[^\n\\][^']|'\\.[^']);
ws = [\ \t\011\012\r];

%%

<INITIAL> {ws}+       => (lex ());
<INITIAL> \n          => (PS.newline(yypos);
			  if annoNewLine()
			  then (ANNO_END, (yypos, yypos+1), NONE)
			  else lex());

<INITIAL> "{"         => ((LBRACE, (yypos, yypos + size yytext), NONE));
<INITIAL> "}"         => ((RBRACE, (yypos, yypos + size yytext), NONE));
<INITIAL> "("         => ((LPAREN, (yypos, yypos + size yytext), NONE));
<INITIAL> ")"         => ((RPAREN, (yypos, yypos + size yytext), NONE));
<INITIAL> "["         => ((LBRACKET, (yypos, yypos + size yytext), NONE));
<INITIAL> "]"         => ((RBRACKET, (yypos, yypos + size yytext), NONE));

<INITIAL> ","         => ((COMMA, (yypos, yypos + size yytext), NONE));
<INITIAL> ":"         => ((COLON, (yypos, yypos + size yytext), NONE));
<INITIAL> ";"         => ((SEMI, (yypos, yypos + size yytext), NONE));
<INITIAL> "."         => ((DOT, (yypos, yypos + size yytext), NONE));

<INITIAL> "="         => ((EQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "+="        => ((PLUSEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "-="        => ((MINUSEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "*="        => ((STAREQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "/="        => ((SLASHEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "%="        => ((PERCENTEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "&="        => ((AMPEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "^="        => ((CARETEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "|="        => ((BAREQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "<<="       => ((LLEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> ">>="       => ((GGEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "++"        => ((PLUSPLUS, (yypos, yypos + size yytext), NONE));
<INITIAL> "--"        => ((MINUSMINUS, (yypos, yypos + size yytext), NONE));

<INITIAL> "+"         => ((PLUS, (yypos, yypos + size yytext), NONE));
<INITIAL> "-"         => ((MINUS, (yypos, yypos + size yytext), NONE));
<INITIAL> "*"         => ((STAR, (yypos, yypos + size yytext), NONE));
<INITIAL> "/"         => ((SLASH, (yypos, yypos + size yytext), NONE));
<INITIAL> "%"         => ((PERCENT, (yypos, yypos + size yytext), NONE));
<INITIAL> "<"         => ((LESS, (yypos, yypos + size yytext), NONE));
<INITIAL> "<="        => ((LESSEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> ">"         => ((GREATER, (yypos, yypos + size yytext), NONE));
<INITIAL> ">="        => ((GREATEREQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "=="        => ((EQEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "!="        => ((BANGEQ, (yypos, yypos + size yytext), NONE));
<INITIAL> "&&"        => ((AMPAMP, (yypos, yypos + size yytext), NONE));
<INITIAL> "||"        => ((BARBAR, (yypos, yypos + size yytext), NONE));
<INITIAL> "&"         => ((AMP, (yypos, yypos + size yytext), NONE));
<INITIAL> "^"         => ((CARET, (yypos, yypos + size yytext), NONE));
<INITIAL> "|"         => ((BAR, (yypos, yypos + size yytext), NONE));
<INITIAL> "<<"        => ((LL, (yypos, yypos + size yytext), NONE));
<INITIAL> ">>"        => ((GG, (yypos, yypos + size yytext), NONE));
<INITIAL> "!"         => ((BANG, (yypos, yypos + size yytext), NONE));
<INITIAL> "~"         => ((TILDE, (yypos, yypos + size yytext), NONE));
<INITIAL> "->"        => ((ARROW,(yypos, yypos + size yytext), NONE));

<INITIAL> "?"         => ((QUESTIONMARK, (yypos, yypos + size yytext), NONE));

<INITIAL> "struct"    => ((STRUCT, (yypos, yypos + size yytext), NONE));
<INITIAL> "typedef"   => ((TYPEDEF, (yypos, yypos + size yytext), NONE));
<INITIAL> "int"       => ((INT, (yypos, yypos + size yytext), NONE));
<INITIAL> "bool"      => ((BOOL, (yypos, yypos + size yytext), NONE));
<INITIAL> "char"      => ((CHAR, (yypos, yypos + size yytext), NONE));
<INITIAL> "string"    => ((STRING_TAU, (yypos, yypos + size yytext), NONE));
<INITIAL> "void"      => ((VOID, (yypos, yypos + size yytext), NONE));
<INITIAL> "if"        => ((IF, (yypos, yypos + size yytext), NONE));
<INITIAL> "else"      => ((ELSE, (yypos, yypos + size yytext), NONE));
<INITIAL> "for"       => ((FOR, (yypos, yypos + size yytext), NONE));
<INITIAL> "while"     => ((WHILE, (yypos, yypos + size yytext), NONE));
<INITIAL> "continue"  => ((CONTINUE, (yypos, yypos + size yytext), NONE));
<INITIAL> "break"     => ((BREAK, (yypos, yypos + size yytext), NONE));
<INITIAL> "return"    => ((RETURN, (yypos, yypos + size yytext), NONE));
<INITIAL> "true"      => ((TRUE, (yypos, yypos + size yytext), NONE));
<INITIAL> "false"     => ((FALSE, (yypos, yypos + size yytext), NONE));
<INITIAL> "NULL"      => ((NULL, (yypos, yypos + size yytext), NONE));
<INITIAL> "alloc"     => ((ALLOC, (yypos, yypos + size yytext), NONE));
<INITIAL> "alloc_array" => ((ALLOC_ARRAY, (yypos, yypos + size yytext), NONE));

<INITIAL> "\\result"  => ((BS_RESULT, (yypos, yypos + size yytext), NONE));
<INITIAL> "\\length"  => ((BS_LENGTH, (yypos, yypos + size yytext), NONE));
<INITIAL> "\\old"     => ((BS_OLD, (yypos, yypos + size yytext), NONE));
<INITIAL> "requires"  => ((REQUIRES, (yypos, yypos + size yytext), NONE));
<INITIAL> "ensures"   => ((ENSURES, (yypos, yypos + size yytext), NONE));
<INITIAL> "loop_invariant"  => ((LOOP_INVARIANT, (yypos, yypos + size yytext), NONE));
<INITIAL> "assert"    => ((ASSERT, (yypos, yypos + size yytext), NONE));

<INITIAL> {decnum}    => ((DECCONST, (yypos, yypos + size yytext), SOME(yytext)));
<INITIAL> {hexnum}    => ((HEXCONST, (yypos, yypos + size yytext), SOME(yytext)));
<INITIAL> {id}        => ((IDENT, (yypos, yypos + size yytext), SOME(yytext)));

<INITIAL> {simplechar} => (convertChar(yytext, yypos));
<INITIAL> {escapechar} => (convertChar(yytext, yypos));
<INITIAL> {badchar}    =>  (ErrorMsg.error (PS.ext (yypos, yypos + size yytext)) "Character constant too long";
                           raise ErrorMsg.Error);
<INITIAL> \"          => (YYBEGIN STRING; initString(yypos); lex());
<INITIAL> @           => (atChars(yytext, yypos); lex());
<INITIAL> "/*@"       => (enterAnno(yytext, yypos); (ANNO_BEGIN, (yypos, yypos + size yytext), NONE));
<INITIAL> "/*"        => (YYBEGIN COMMENT; enterComment yypos; lex());
<INITIAL> "@*/"       => (exitAnno(yytext, yypos); (ANNO_END, (yypos, yypos + size yytext), NONE));
<INITIAL> "*/"        => (ErrorMsg.error (PS.ext (yypos, yypos)) "unbalanced comments";
                          lex());

<INITIAL> "//@"       => (enterAnnoLine(yytext, yypos); (ANNO_BEGIN, (yypos, yypos + size yytext), NONE));
<INITIAL> "//"        => (enterCommentLine(); YYBEGIN COMMENT_LINE; lex());
<INITIAL> #{id}       => (YYBEGIN PRAGMA; initPragma(yytext, yypos); lex());
<INITIAL> #           => (YYBEGIN PRAGMA; initPragma(yytext, yypos); lex());
<INITIAL> .           => (ErrorMsg.error (PS.ext (yypos,yypos))
		            ("illegal character: \"" ^ yytext ^ "\"");
					      raise ErrorMsg.Error;
                          lex ());

<STRING> \"           => (YYBEGIN INITIAL; convertString(yypos));
<STRING> \n           => (ErrorMsg.error (PS.ext (yypos,yypos))
			    ("illegal newline in string; use \\n");
			  PS.newline(yypos);
			  lex());
<STRING> [^"\\\n]*    => (addString(yytext); lex());
<STRING> \\\n         => (addSpecialChar(yytext,yypos); lex());
<STRING> \\.          => (addSpecialChar(yytext,yypos); lex());
<STRING> .            => (ErrorMsg.error (PS.ext (yypos,yypos))
			    ("illegal character in string: `" ^ yytext ^ "'");
			  lex ());

<COMMENT> "/*"        => (enterComment yypos; lex());
<COMMENT> "*/"        => (if exitComment () then YYBEGIN INITIAL else (); lex());
<COMMENT> \n          => (PS.newline(yypos); newLineInComment(yypos); lex ());
<COMMENT> .           => (lex());

<COMMENT_LINE> \n     => (PS.newline(yypos); YYBEGIN INITIAL;
			  if annoNewLine()
			  then (exitCommentLine(); (ANNO_END,(yypos, yypos+1), NONE))
			  else (exitCommentLine(); lex()));
<COMMENT_LINE> .      => (lex());

<PRAGMA> \n           => (PS.newline(yypos); YYBEGIN INITIAL; convertPragma(yypos));
<PRAGMA> [^\\\n]*     => (addString(yytext); lex());
<PRAGMA> \\\n         => (PS.newline(yypos); addString(yytext); lex());
<PRAGMA> \\.          => (addString(yytext); lex());
