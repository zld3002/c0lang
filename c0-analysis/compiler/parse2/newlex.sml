(* C0 Compiler
 * Lexing 
 * Rob Simmons
 *
 * Nearly-stateless lexer. In order to smootly integrate with the interactive 
 * top-level, this lexer takes a persistent stream and returns a token, a new 
 * persistent stream, and an object representing the internal state of the
 * lexer. The point of the lexer is that it can have its legs kicked out from
 * underneath it at any line break and can then pick back up when the user
 * provides more input.
 *
 * If the "quiet" flag is false (default value) then the lexer uses the 
 * effectful ErrorMsg structure to print and record errors. If the "quiet" flag
 * is true then nothing is printed and errors are not recorded in the ErrorMsg 
 * structure. *)

structure C0Lex :> sig
   eqtype state 
   val normal : state 
   val quiet : bool ref

   type stream (* Persistant data structure *)
   (* Turns a string into a stream *)
   val str_stream : string -> stream
   (* Turns a stateful data source (one that returns "" if there is no more 
    * input) into a stream. *)
   val buffered_stream : (int -> string) -> stream 

   (* ML-Lex style lexer interface *)
   structure UserDeclarations : sig
      include C0_TERMINAL 
      type lexresult = terminal * (int * int) * string option
      type lexanswer = terminal * int * int * string option * stream * state
   end
   
   val makeLexer : (int -> string) -> (unit -> UserDeclarations.lexresult)

   (* Interactive lexer *)
   val lex : int * stream * state -> UserDeclarations.lexanswer
end = struct

(* Simple stream interface *)
datatype front = N | C of char * (unit -> front)
type stream = (unit -> front)
fun force stream = stream ()

(* States *)
datatype code_state = NORMAL | ANNO | ANNO_LINE
datatype state = 
    CODE of code_state
  | COMMENT of int * code_state
  | COMMENT_LINE of code_state
  | ESCAPE_PRAGMA of char list 
  | NORMAL_PRAGMA of char list 
val normal = CODE NORMAL

(* Boilerplate *)
structure PS = ParseState
structure UserDeclarations = (* Compatibility reasons *)
struct 
   open C0Terminal 
   type lexresult = terminal * (int * int) * string option
   type lexanswer = terminal * int * int * string option * stream * state
end
open UserDeclarations

(* Error reporting *)
val quiet = ref false
fun error pos msg = if !quiet then () else ErrorMsg.error (PS.ext pos) msg

(* Functionally, a near-duplicate of Char.fromCString *)
fun special_char c pos = 
   case c of 
      #"n" => SOME #"\n"
    | #"t" => SOME #"\t"
    | #"v" => SOME #"\v"
    | #"b" => SOME #"\b"
    | #"r" => SOME #"\r"
    | #"f" => SOME #"\f"
    | #"a" => SOME #"\a"
    | #"\\" => SOME #"\\"
    (* \? no longer accepted, according to C0 language spec *)
    (* | #"?" => SOME #"?" *)
    | #"'" => SOME #"'"
    | #"\"" => SOME #"\""
    | c => NONE before error (pos, pos+1)
         ("illegal escape sequence `\\" ^ Char.toString c ^ "'")

(* Grab a complete string *)
fun lex_string (pos, charstream, string) : int * stream * string option = 
   case force charstream of
      N => (pos, charstream, NONE) 
      before error (pos, pos) "string constant not terminated"
    | C (#"\"", cs) => 
      let
         fun collect_rev (chars, str) = 
           case chars of 
              [] => SOME (String.implode str)
            | (NONE :: _) => NONE
            | (SOME c :: cs) => collect_rev (cs, c :: str)
      in (pos+1, cs, collect_rev (string, [])) end
    | C (#"\n", cs) => 
      (PS.newline pos
       ; error (pos, pos+1) "illegal newline in string; use `\\n'"
       ; lex_string (pos+1, cs, NONE :: string))
    | C (#"\\", cs) => 
      (case force cs of 
          N => lex_string (pos+1, cs, NONE :: string)
        | C (c, cs) => lex_string (pos+2, cs, special_char c pos :: string))
    | C (c, cs) => lex_string (pos+1, cs, SOME c :: string)

(* "Normal" lexing *)
fun lex_code (pos, charstream, code_state) = 
   let
      val cs = charstream
      val s = CODE code_state
      fun run_cond cond (n, s, cs) = 
         case force cs of
            N => (String.implode (rev s), n, cs)
          | C (c, cs') =>
            if cond c
            then run_cond cond (n+1, c :: s, cs')
            else (String.implode (rev s), n, cs)
      val run_alpha = run_cond (fn c => Char.isAlphaNum c orelse c = #"_")
      val run_number = run_cond Char.isDigit
      val run_hex = run_cond Char.isHexDigit
   in
      case force charstream of 
       (* End of file *)
         N => (EOF, pos, pos, NONE, charstream, s)

       (* Whitespace *)
       | C (#" ", cs) => lex_code (pos+1, cs, code_state)
       | C (#"\t", cs) => lex_code (pos+1, cs, code_state)
       | C (#"\011", cs) => lex_code (pos+1, cs, code_state)
       | C (#"\012", cs) => lex_code (pos+1, cs, code_state)
       | C (#"\r", cs) => lex_code (pos+1, cs, code_state)
       | C (#"\n", cs) => 
         (PS.newline pos
          ; case code_state of
               ANNO_LINE => (ANNO_END,    pos, pos+1, NONE, cs, CODE NORMAL)
             | _ => lex_code (pos+1, cs, code_state))

       (* Separators *)
       | C (#"{", cs) => (LBRACE,         pos, pos+1, NONE, cs, s)
       | C (#"}", cs) => (RBRACE,         pos, pos+1, NONE, cs, s)
       | C (#"(", cs) => (LPAREN,         pos, pos+1, NONE, cs, s)
       | C (#")", cs) => (RPAREN,         pos, pos+1, NONE, cs, s)
       | C (#"[", cs) => (LBRACKET,       pos, pos+1, NONE, cs, s)
       | C (#"]", cs) => (RBRACKET,       pos, pos+1, NONE, cs, s)
       | C (#",", cs) => (COMMA,          pos, pos+1, NONE, cs, s)
       | C (#":", cs) => (COLON,          pos, pos+1, NONE, cs, s)
       | C (#";", cs) => (SEMI,           pos, pos+1, NONE, cs, s)
       | C (#".", cs) => (DOT,            pos, pos+1, NONE, cs, s)
       | C (#"~", cs) => (TILDE,          pos, pos+1, NONE, cs, s)
       | C (#"?", cs) => (QUESTIONMARK,   pos, pos+1, NONE, cs, s)

       (* Math *)
       | C (#"=", cs) => 
         (case force cs of
             C (#"=", cs) => (EQEQ,       pos, pos+2, NONE, cs, s)
           | _ => (EQ,                    pos, pos+1, NONE, cs, s))
       | C (#"+", cs) => 
         (case force cs of
             C (#"=", cs) => (PLUSEQ,     pos, pos+2, NONE, cs, s)
           | C (#"+", cs) => (PLUSPLUS,   pos, pos+2, NONE, cs, s)
           | _ => (PLUS,                  pos, pos+1, NONE, cs, s))
       | C (#"-", cs) => 
         (case force cs of 
             C (#"=", cs) => (MINUSEQ,    pos, pos+2, NONE, cs, s)
           | C (#"-", cs) => (MINUSMINUS, pos, pos+2, NONE, cs, s)
           | C (#">", cs) => (ARROW,      pos, pos+2, NONE, cs, s)
           | _ => (MINUS,                 pos, pos+1, NONE, cs, s))
       | C (#"*", cs) => 
         (case force cs of
             C (#"=", cs) => (STAREQ,     pos, pos+2, NONE, cs, s)
           | _ => (STAR,                  pos, pos+1, NONE, cs, s))
       | C (#"#", cs) => 
         if (code_state <> NORMAL)
         then (ERROR,                     pos, pos+1, NONE, cs, s)
                  before error (pos, pos+1) "#pragma in annotation"
         else lex_pragma (pos+1, cs, [ #"#" ])
       | C (#"/", cs) => 
         (case force cs of
             C (#"=", cs) => (SLASHEQ,    pos, pos+2, NONE, cs, s)
           | C (#"/", cs) => 
             (case force cs of
                C (#"@", cs) => 
                (case code_state of
                    NORMAL => (ANNO_BEGIN,pos, pos+3, NONE, cs, CODE ANNO_LINE)
                  | _ => (ERROR,          pos, pos+3, NONE, cs, s)
                    before error (pos, pos+3) "no nested annotations")
              | _ => lex_comment_line (pos+2, cs, code_state))
           | C (#"*", cs) => 
             (case force cs of
                C (#"@", cs) =>
                (case code_state of
                    NORMAL => (ANNO_BEGIN,pos, pos+3, NONE, cs, CODE ANNO)
                  | _ => (ERROR,          pos, pos+3, NONE, cs, s)
                    before error (pos, pos+3) "no nested annotations")
              | _ => lex_comment (pos+2, cs, 1, code_state))
           | _ => (SLASH,                 pos, pos+1, NONE, cs, s))
       | C (#"%", cs) => 
         (case force cs of
             C (#"=", cs) => (PERCENTEQ,  pos, pos+2, NONE, cs, s)
           | _ => (PERCENT,               pos, pos+1, NONE, cs, s))
       | C (#"&", cs) => 
         (case force cs of
             C (#"=", cs) => (AMPEQ,      pos, pos+2, NONE, cs, s)
           | C (#"&", cs) => (AMPAMP,     pos, pos+2, NONE, cs, s)
           | _ => (AMP,                   pos, pos+1, NONE, cs, s))
       | C (#"^", cs) => 
         (case force cs of
             C (#"=", cs) => (CARETEQ,    pos, pos+2, NONE, cs, s)
           | _ => (CARET,                 pos, pos+1, NONE, cs, s))
       | C (#"|", cs) => 
         (case force cs of
             C (#"=", cs) => (BAREQ,      pos, pos+2, NONE, cs, s)
           | C (#"|", cs) => (BARBAR,     pos, pos+2, NONE, cs, s)
           | _ => (BAR,                   pos, pos+1, NONE, cs, s))
       | C (#"!", cs) => 
         (case force cs of
             C (#"=", cs) => (BANGEQ,     pos, pos+2, NONE, cs, s)
           | _ => (BANG,                  pos, pos+1, NONE, cs, s))
       | C (#"<", cs) => 
         (case force cs of
             C (#"=", cs) => (LESSEQ,     pos, pos+2, NONE, cs, s)
           | C (#"<", cs) => 
             (case force cs of
                 C (#"=", cs) => (LLEQ,   pos, pos+3, NONE, cs, s)
               | _ => (LL,                pos, pos+2, NONE, cs, s))
           | _ => (LESS,                  pos, pos+1, NONE, cs, s))
       | C (#">", cs) => 
         (case force cs of
             C (#"=", cs) => (GREATEREQ,  pos, pos+2, NONE, cs, s)
           | C (#">", cs) => 
             (case force cs of
                 C (#"=", cs) => (GGEQ,   pos, pos+3, NONE, cs, s)
               | _ => (GG,                pos, pos+2, NONE, cs, s))
           | _ => (GREATER,               pos, pos+1, NONE, cs, s))

       (* The curious case of @ - whitespace, but only in annotations *)
       | C (#"@", cs) =>
         let val end_anno = 
            case force cs of 
               C (#"*", cs) => 
               (case force cs of C (#"/", cs) => SOME cs | _ => NONE)
             | _ => NONE
         in 
            case end_anno of
               NONE => 
               (if code_state <> NORMAL then lex_code (pos+1, cs, code_state)
                else ((ERROR,             pos, pos+1, NONE, cs, s)
                before error (pos, pos)
                      "character `@' is illegal outside of an annotation"))
             | SOME cs => 
               (if code_state = ANNO 
                then (ANNO_END,           pos, pos+3, NONE, cs, CODE NORMAL)
                else ((ERROR,             pos, pos+3, NONE, cs, s)
                before error (pos, pos+3)
                      "token `@*/' outside delimited annotation"))
         end

       (* Escaped identifiers *)
       | C (#"\\", cs) => 
         (case run_alpha (1, [], cs) of
             ("result", n, cs) => (BS_RESULT, pos, pos+n, NONE, cs, s)
           | ("length", n, cs) => (BS_LENGTH, pos, pos+n, NONE, cs, s)
           | ("old", n, cs) => (BS_OLD,       pos, pos+n, NONE, cs, s)
           | (bs, n, cs) => (ERROR,           pos, pos+n, NONE, cs, s)
             before error (pos, pos)
                ("illegal escaped identifier: `\\" ^ bs ^ "'"))
                              
       (* Char constants *)
       | C (#"'", cs) =>
         let 
            val (c, cs, pos') =
            case force cs of 
               N => (NONE, cs, pos+1)
               before error (pos, pos+1) "incomplete char constant" 
             | C (#"\\", cs) => 
               (case force cs of 
                   N => (NONE, cs, pos+2)
                   before error (pos, pos+1) "incomplete char constant"
                 | C (c, cs) => 
                   let val s = "\\" ^ str c 
                   in (SOME s, cs, pos+3) end)
             | C (#"\n", cs) => (NONE, cs, pos+2)
               before error (pos, pos+2) "illegal newline in char; use `\\n'"
             | C (c, cs) => 
               if Char.isPrint c 
               then (SOME (str c), cs, pos+2)
               else ((NONE, cs, pos+2)
                     before error (pos, pos+2) "non-printable character")
         in 
            case (c, force cs) of 
               (SOME c, C (#"'", cs)) => 
               (CHARCONST, pos, pos'+1, SOME c, cs, s)
             | (_, N) => (ERROR,                 pos, pos', NONE, cs, s)
               before error (pos, pos')
               "incomplete char constant: expected `'' but found end of input"
             | (NONE, C (#"'", cs)) => (ERROR,   pos, pos'+1, NONE, cs, s)
             | (NONE, _) => (ERROR,              pos, pos', NONE, cs, s)
             | (SOME _, C (c, _)) => (ERROR,    pos, pos', NONE, cs, s) 
               before error (pos, pos'+1)
               ("bad char constant: expected `'' but found `"
                ^ Char.toCString c ^ "'")
         end
             
       (* String constants *)
       | C (#"\"", cs) => 
         let val (pos', cs, string) = lex_string (pos+1, cs, []) in
            case string of 
               NONE => (ERROR,            pos, pos', NONE, cs, s)
             | SOME str => (STRINGCONST,  pos, pos', SOME str, cs, s)
         end

       (* Some decimal constants; all hexidecimal constants *)
       | C (#"0", cs') =>
         (case force cs' of
             C (#"x", cs) => 
             let val (num, n, cs) = run_hex (2, [], cs)
             in (HEXCONST,                pos, pos+n, SOME num, cs, s) end
           | C (#"X", cs) => 
             let val (num, n, cs) = run_hex (2, [], cs)
             in (HEXCONST,                pos, pos+n, SOME num, cs, s) end
           | C (c, cs'') => 
             if Char.isDigit c 
             then (ERROR,                 pos, pos+2, NONE, cs'', s)
                  before error (pos, pos+2)
                  "non-zero integer constants cannot start with `0'"
             else (DECCONST,              pos, pos+1, SOME "0", cs', s)
           | N => (DECCONST,              pos, pos+1, SOME "0", cs', s))

       (* Keywords, numbers, and identifiers *)
       | C (c, cs') => 
         (if Char.isAlpha c orelse c = #"_"
          then 
          (case run_alpha (0, [], charstream) of
              ("struct",  n, cs) =>     (STRUCT, pos, pos+n, NONE, cs, s)
            | ("typedef", n, cs) =>     (TYPEDEF, pos, pos+n, NONE, cs, s)
            | ("int",     n, cs) =>     (INT, pos, pos+n, NONE, cs, s)
            | ("bool", n, cs) =>        (BOOL, pos, pos+n, NONE, cs, s)
            | ("char", n, cs) =>        (CHAR, pos, pos+n, NONE, cs, s)
            | ("string", n, cs) =>      (STRING_TAU, pos, pos+n, NONE, cs, s)
            | ("void", n, cs) =>        (VOID, pos, pos+n, NONE, cs, s)
            | ("if", n, cs) =>          (IF, pos, pos+n, NONE, cs, s)
            | ("else", n, cs) =>        (ELSE, pos, pos+n, NONE, cs, s)
            | ("for", n, cs) =>         (FOR, pos, pos+n, NONE, cs, s)
            | ("while", n, cs) =>       (WHILE, pos, pos+n, NONE, cs, s)
            | ("continue", n, cs) =>    (CONTINUE, pos, pos+n, NONE, cs, s)
            | ("break", n, cs) =>       (BREAK, pos, pos+n, NONE, cs, s)
            | ("return", n, cs) =>      (RETURN, pos, pos+n, NONE, cs, s)
            | ("true", n, cs) =>        (TRUE, pos, pos+n, NONE, cs, s)
            | ("false", n, cs) =>       (FALSE, pos, pos+n, NONE, cs, s)
            | ("NULL", n, cs) =>        (NULL, pos, pos+n, NONE, cs, s)
            | ("alloc", n, cs) =>       (ALLOC, pos, pos+n, NONE, cs, s)
            | ("alloc_array", n, cs) => (ALLOC_ARRAY, pos, pos+n, NONE, cs, s)
            | ("requires", n, cs) =>    (REQUIRES, pos, pos+n, NONE, cs, s)
            | ("ensures", n, cs) =>     (ENSURES, pos, pos+n, NONE, cs, s)
            | ("loop_invariant", n, cs) => 
              (LOOP_INVARIANT, pos, pos+n, NONE, cs, s)
            | ("assert", n, cs) =>      (ASSERT, pos, pos+n, NONE, cs, s)
            | (ident, n, cs) =>         (IDENT, pos, pos+n, SOME ident, cs, s))
          (* Numerical constants *)
          else if Char.isDigit c 
          then 
          (let val (num, n, cs) = run_number (0, [], charstream)
           in (DECCONST, pos, pos+n, SOME num, cs, s) end)
          else (ERROR, pos, pos+1, NONE, cs', s)
             before error (pos, pos)
             ("illegal character: `" ^ Char.toString c ^ "'"))
   end

and lex_comment (pos, charstream, depth, prev) = 
   case force charstream of
      N => (EOF, pos, pos, NONE, charstream, COMMENT (depth, prev))
    | C (#"\n", cs) => 
      (PS.newline pos
       ; case prev of
            ANNO_LINE => error (pos, pos+1)
            "end of delimited comment in single-line annotation"
          | _ => ()
       ; lex_comment (pos+1, cs, depth, prev))
    | C (#"/", cs) =>
      (case force cs of
          C (#"*", cs) => lex_comment (pos+2, cs, depth+1, prev)
        | _ => lex_comment (pos+1, cs, depth, prev))
    | C (#"*", cs) =>
      (case force cs of
          C (#"/", cs) => 
          (if depth <= 1 then lex_code (pos+2, cs, prev)
           else lex_comment (pos+2, cs, depth-1, prev))
        | _ => lex_comment (pos+1, cs, depth, prev))
    | C (_, cs) => lex_comment (pos+1, cs, depth, prev)

and lex_escape_pragma (pos, charstream, pragma) = 
   case force charstream of
      N => (EOF, pos, pos, NONE, charstream, ESCAPE_PRAGMA pragma)
    | C (#"\n", cs) => 
      (PS.newline pos; lex_pragma (pos+1, cs, #"\n" :: pragma))
    | C (c, cs) => lex_pragma (pos+1, cs, c :: pragma)

and lex_pragma (pos, charstream, pragma) = 
   case force charstream of
      N => (EOF, pos, pos, NONE, charstream, NORMAL_PRAGMA pragma)
    | C (#"\\", cs) => lex_escape_pragma (pos+1, cs, #"\\" :: pragma)
    | C (#"\n", cs) => 
      let val old_pos = pos - length pragma in
         PS.newline pos
         ; (PRAGMA, old_pos, pos, SOME (implode (rev pragma)), cs, CODE NORMAL) 
      end
    | C (c, cs) => lex_pragma (pos+1, cs, c :: pragma)
       

and lex_comment_line (pos, charstream, prev) = 
   case force charstream of
      N => (EOF, pos, pos, NONE, charstream, COMMENT_LINE prev)
    | C (#"\n", cs) => 
      (PS.newline pos
       ; case prev of
            ANNO_LINE => (ANNO_END, pos, pos+1, NONE, cs, CODE NORMAL)
          | _ => lex_code (pos+1, cs, prev))
    | C (_, cs) => lex_comment_line (pos+1, cs, prev)

fun lex (pos, charstream, state) =
   case state of
      CODE code_state => lex_code (pos, charstream, code_state)
    | COMMENT (depth, prev) => lex_comment (pos, charstream, depth, prev)
    | COMMENT_LINE prev => lex_comment_line (pos, charstream, prev)
    | ESCAPE_PRAGMA pragma => lex_escape_pragma (pos, charstream, pragma)
    | NORMAL_PRAGMA pragma => lex_pragma (pos, charstream, pragma)

fun buffered_stream source = 
   let
      fun use_buf (str, len, i) = 
         if i = len 
         then refill_buf ()
         else fn () => C (String.sub (str, i), use_buf (str, len, i+1))

      and refill_buf () =
          let
              val memo = ref (fn () => raise Match)
              fun read () =
                 let val ans = 
                    case source 1024 of 
                       "" => N
                     | s => C (String.sub (s, 0), use_buf (s, size s, 1))
                 in memo := (fn () => ans); ans end
          in memo := read; (fn () => (!memo) ()) end
   in refill_buf () end

fun str_stream str = 
    let val r = ref false
    in buffered_stream (fn _ => if !r then "" else (r := true; str)) end

type lexresult = terminal * (int * int) * string option

fun makeLexer source = 
   let
      val state = ref (1, buffered_stream source, CODE NORMAL)
      fun loop () =
         let val (tok, left_pos, right_pos, data, new_stream, new_state)
            = lex (!state)
            fun eof state = 
               case state of 
                  CODE NORMAL => ()
                | CODE ANNO => error (left_pos, right_pos)
                  "delimited annotation not terminated"
                | CODE ANNO_LINE => error (left_pos, right_pos)
                  ("single line annotation not terminated with newline " 
                   ^ "at end of file")
                | COMMENT _ => error (left_pos, right_pos)
                  "comment not terminated"
                | COMMENT_LINE _ => error (left_pos, right_pos)
                  ("single line comment not terminated by newline " 
                   ^ "at end of file")
                | ESCAPE_PRAGMA _ => error (left_pos, right_pos)
                  ("#pragma not terminated by newline at end of file")
                | NORMAL_PRAGMA _ => error (left_pos, right_pos)
                  ("#pragma not terminated by newline at end of file")
         in
            if tok = EOF then eof new_state else ()
            ; state := (right_pos, new_stream, new_state)
            ; (tok, (left_pos, right_pos), data)
         end
   in loop end
   
end
