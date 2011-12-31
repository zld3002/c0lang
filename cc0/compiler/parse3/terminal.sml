(* C0 Compiler
 * Terminals
 * Rob Simmons, Frank Pfenning
 *)

signature TERMINAL = sig

datatype terminal =
   INT | BOOL | STRING | CHAR | VOID | STRUCT | TYPEDEF
 | IF | ELSE | WHILE | FOR | CONTINUE | BREAK | RETURN | ASSERT
 | TRUE | FALSE | NULL | ALLOC | ALLOC_ARRAY
 | IDENT of string | DECNUM of string | HEXNUM of string
 | STRLIT of string | CHRLIT of string
 | DOT | ARROW
 | EXCL | TILDE | MINUS | STAR
 | PLUS | SLASH | PERCENT | LL | GG
 | LESS | LEQ | GEQ | GREATER | EQEQ | EXCLEQ 
 | AMP | CARET | BAR | AMPAMP | BARBAR
 | QUEST | COLON
 | EQ | PLUSEQ | MINUSEQ | STAREQ | SLASHEQ | PERCENTEQ | LLEQ | GGEQ
 | AMPEQ | CARETEQ | BAREQ
 | PLUSPLUS | MINUSMINUS
 | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE
 | COMMA | SEMI
 | ANNO_BEGIN | ANNO_END
 | REQUIRES | ENSURES | LOOP_INVARIANT
 | BS_RESULT | BS_LENGTH | BS_OLD
 | PRAGMA of string | EOF | EOL | ERROR

val toString : terminal -> string

end

structure Terminal :> TERMINAL = struct

datatype terminal =
   INT | BOOL | STRING | CHAR | VOID | STRUCT | TYPEDEF
 | IF | ELSE | WHILE | FOR | CONTINUE | BREAK | RETURN | ASSERT
 | TRUE | FALSE | NULL | ALLOC | ALLOC_ARRAY
 | IDENT of string | DECNUM of string | HEXNUM of string
 | STRLIT of string | CHRLIT of string
 | DOT | ARROW
 | EXCL | TILDE | MINUS | STAR
 | PLUS | SLASH | PERCENT | LL | GG
 | LESS | LEQ | GEQ | GREATER | EQEQ | EXCLEQ 
 | AMP | CARET | BAR | AMPAMP | BARBAR
 | QUEST | COLON
 | EQ | PLUSEQ | MINUSEQ | STAREQ | SLASHEQ | PERCENTEQ | LLEQ | GGEQ
 | AMPEQ | CARETEQ | BAREQ
 | PLUSPLUS | MINUSMINUS
 | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE
 | COMMA | SEMI
 | ANNO_BEGIN | ANNO_END
 | REQUIRES | ENSURES | LOOP_INVARIANT
 | BS_RESULT | BS_LENGTH | BS_OLD
 | PRAGMA of string | EOF | EOL | ERROR

fun toString t = case t of
   INT => "int" | BOOL => "bool" | STRING => "string" | CHAR => "char" | VOID => "void"
 | STRUCT => "struct" | TYPEDEF => "typedef"
 | IF => "if" | ELSE => "else" | WHILE => "while" | FOR => "for"
 | CONTINUE => "continue" | BREAK => "break" | RETURN => "return" | ASSERT => "assert"
 | TRUE => "true" | FALSE => "false" | NULL => "NULL" | ALLOC => "alloc" | ALLOC_ARRAY => "alloc_array"
 | IDENT(s) => s | DECNUM(s) => s | HEXNUM(s) => s
 | STRLIT(s) => "\"" ^ s ^ "\"" | CHRLIT(s) => "'" ^ s ^ "'"
 | DOT => "." | ARROW => "->"
 | EXCL => "!" | TILDE => "~" | MINUS => "-" | STAR => "*"
 | PLUS => "+" | SLASH => "/" | PERCENT => "%" | LL => "<<" | GG => ">>"
 | LESS => "<" | LEQ => "<=" | GEQ => ">=" | GREATER => ">" | EQEQ => "==" | EXCLEQ => "!="
 | AMP => "&" | CARET => "^" | BAR => "|" | AMPAMP => "&&" | BARBAR => "||"
 | QUEST => "?" | COLON => ":"
 | EQ => "=" | PLUSEQ => "+=" | MINUSEQ => "-=" | STAREQ => "*=" | SLASHEQ => "/=" | PERCENTEQ => "%="
 | LLEQ => "<<=" | GGEQ => ">>=" | AMPEQ => "&=" | CARETEQ => "^=" | BAREQ => "|="
 | PLUSPLUS => "++" | MINUSMINUS => "--"
 | LPAREN => "(" | RPAREN => ")" | LBRACKET => "[" | RBRACKET => "]" | LBRACE => "{" | RBRACE => "}"
 | COMMA => "," | SEMI => ";"
 | ANNO_BEGIN => "/*@" | ANNO_END => "@*/"
 | REQUIRES => "requires" | ENSURES => "ensures" | LOOP_INVARIANT => "loop_invariant"
 | BS_RESULT => "\\result" | BS_LENGTH => "\\length" | BS_OLD => "\\old"
 | PRAGMA(s) => "#<pragma>" | EOF => "<eof>" | EOL => "<eol>" | ERROR => "<lex error>"

end
