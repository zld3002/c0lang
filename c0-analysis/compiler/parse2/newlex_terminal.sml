(* C0 Compiler
 * Terminals
 * Rob Simmons *)

signature C0_TERMINAL = sig

datatype terminal =
   BS_OLD | BS_LENGTH | BS_RESULT
 | ASSERT | LOOP_INVARIANT 
 | ENSURES | REQUIRES 
 | ANNO_END | ANNO_BEGIN 
 | RBRACKET | LBRACKET | RPAREN | LPAREN 
 | RBRACE | LBRACE | MINUSMINUS | PLUSPLUS 
 | GGEQ | LLEQ | BAREQ | CARETEQ 
 | AMPEQ | PERCENTEQ | SLASHEQ | STAREQ 
 | MINUSEQ | PLUSEQ | EQ | ARROW | DOT 
 | TILDE | BANG | GG | LL | BAR 
 | CARET | AMP | BARBAR | AMPAMP 
 | BANGEQ | EQEQ | GREATEREQ | GREATER 
 | LESSEQ | LESS | PERCENT | SLASH 
 | STAR | MINUS | PLUS | ALLOC_ARRAY 
 | ALLOC | NULL | FALSE | TRUE 
 | RETURN | BREAK | CONTINUE 
 | FOR | WHILE | ELSE | IF 
 | VOID | CHAR | STRING_TAU | BOOL 
 | INT | TYPEDEF | STRUCT 
 | CHARCONST | STRINGCONST 
 | TYPENAME | IDENT 
 | VARNAME | LRBRACKETS 
 | DECCONST | HEXCONST 
 | QUESTIONMARK | SEMI | COLON | COMMA 
 | EOF | ERROR | PRAGMA

val tok_string : terminal -> string

end

structure C0Terminal :> C0_TERMINAL = struct

datatype terminal =
   BS_OLD | BS_LENGTH | BS_RESULT
 | ASSERT | LOOP_INVARIANT 
 | ENSURES | REQUIRES 
 | ANNO_END | ANNO_BEGIN 
 | RBRACKET | LBRACKET | RPAREN | LPAREN 
 | RBRACE | LBRACE | MINUSMINUS | PLUSPLUS 
 | GGEQ | LLEQ | BAREQ | CARETEQ 
 | AMPEQ | PERCENTEQ | SLASHEQ | STAREQ 
 | MINUSEQ | PLUSEQ | EQ | ARROW | DOT 
 | TILDE | BANG | GG | LL | BAR 
 | CARET | AMP | BARBAR | AMPAMP 
 | BANGEQ | EQEQ | GREATEREQ | GREATER 
 | LESSEQ | LESS | PERCENT | SLASH 
 | STAR | MINUS | PLUS | ALLOC_ARRAY 
 | ALLOC | NULL | FALSE | TRUE 
 | RETURN | BREAK | CONTINUE 
 | FOR | WHILE | ELSE | IF 
 | VOID | CHAR | STRING_TAU | BOOL 
 | INT | TYPEDEF | STRUCT 
 | CHARCONST | STRINGCONST 
 | TYPENAME | IDENT 
 | VARNAME | LRBRACKETS 
 | DECCONST | HEXCONST 
 | QUESTIONMARK | SEMI | COLON | COMMA 
 | EOF | ERROR | PRAGMA

val tok_string = 
 fn BS_OLD => "\\result" | BS_LENGTH => "\\length" | BS_RESULT => "\\result"
  | ASSERT => "assert" | LOOP_INVARIANT => "loop_invariant" 
  | ENSURES => "ensures" | REQUIRES => "requires" 
  | ANNO_END => "@*/" | ANNO_BEGIN => "/*@"
  | RBRACKET => ")" | LBRACKET => "[" | RPAREN => ")" | LPAREN => "("
  | RBRACE => "}" | LBRACE => "{" | MINUSMINUS => "--" | PLUSPLUS => "++"
  | GGEQ => ">>=" | LLEQ => "<<=" | BAREQ => "|=" | CARETEQ => "^="
  | AMPEQ => "&=" | PERCENTEQ => "%=" | SLASHEQ => "/=" | STAREQ => "*="
  | MINUSEQ => "-=" | PLUSEQ => "+=" | EQ => "=" | ARROW => "->" | DOT => "."
  | TILDE => "~" | BANG => "!" | GG => ">>" | LL => "<<" | BAR => "|"
  | CARET => "^" | AMP => "&" | BARBAR => "||" | AMPAMP => "&&" 
  | BANGEQ => "!=" | EQEQ => "==" | GREATEREQ => ">=" | GREATER => ">"
  | LESSEQ => "<=" | LESS => "<" | PERCENT => "%" | SLASH => "/"
  | STAR => "*" | MINUS => "-" | PLUS => "+" | ALLOC_ARRAY => "alloc_array"
  | ALLOC => "alloc" | NULL => "NULL" | FALSE => "false" | TRUE => "true"
  | RETURN => "return" | BREAK => "break" | CONTINUE => "continue" 
  | FOR => "for" | WHILE => "while" | ELSE => "else" | IF => "if" 
  | VOID => "void" | CHAR => "char" | STRING_TAU => "string" | BOOL => "bool"
  | INT => "int" | TYPEDEF => "typedef" | STRUCT => "struct" 
  | CHARCONST => "<char constant>" | STRINGCONST => "<string constant>"
  | TYPENAME => "<type name>" | IDENT => "<identifier>" 
  | VARNAME => "<var name>" | LRBRACKETS => "[]" 
  | DECCONST => "<decimal constant>" | HEXCONST => "<hex constant>"
  | QUESTIONMARK => "?" | SEMI => ";" | COLON => "," | COMMA => "," 
  | EOF => "<EOF>" | ERROR => "<lex error>" | PRAGMA => "#<pragma>"

end
