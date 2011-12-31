structure NewTokens =
struct

(* This type defines all the different types of tokens in the language *)
type terminal = EOF | INTCONST | CHARCONST | STRINGCONST

(* A token consists of the token type, the start and end positions of the
   token, and possibly a string value (for things like idents or intconsts).
   Intconst strings are converted to ints in the parser, rather than lexer,
   so that I can have a simple, streamlined type here that's easy to pattern
   match on
*)
type token = terminal * (int * int) * string option

end
