(* C0 Compiler
 * Lexing 
 * Rob Simmons
 *
 * Nearly-stateless lexer. In order to smoothly integrate with the interactive 
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
   val toString : state -> string
   val quiet : bool ref (* if true, show no error messages *)
   val warnings : bool ref  (* if true, show warnings *)
   val lexAnnos : bool ref  (* if false, all annotations are comments *)

   (* Turns a string into a character stream *)
   val str_stream : string -> char Stream.stream

   (* Turns a stateful data source (one that returns "" if there is no more 
    * input) into a stream. *)
   val buffered_stream : (int -> string) -> char Stream.stream 

   type lexresult = Terminal.terminal * (int * int)

   (* cc0 interface - stream terminated with EOF *)
   val makeLexer : (int -> string) -> lexresult Stream.stream

   (* coin interface - stream terminated with EOL *)
   val lineLexer: 
      char Stream.stream * int * state -> 
         lexresult Stream.stream * int * state
end = struct

(* States *)
datatype code_state = NORMAL | ANNO | ANNO_LINE
datatype state = 
    CODE of code_state
  | COMMENT of int * code_state
  | COMMENT_LINE of code_state
  | ESCAPE_PRAGMA of char list 
  | NORMAL_PRAGMA of char list 
val normal = CODE NORMAL

fun csToString NORMAL = "code"
  | csToString ANNO = "annotation"
  | csToString ANNO_LINE = "line annotation"

fun toString (CODE cs) = "in " ^ csToString cs 
  | toString (COMMENT (x, cs)) =
       "comment depth " ^ Int.toString x ^ " in " ^ csToString cs
  | toString (COMMENT_LINE cs) = "line comment in " ^ csToString cs
  | toString (ESCAPE_PRAGMA cs) = 
      "escape pragma (size " ^ Int.toString (length cs) ^ ")"
  | toString (NORMAL_PRAGMA cs) = 
      "normal pragma (size " ^ Int.toString (length cs) ^ ")"

(* Boilerplate *)
structure PS = ParseState
structure M = Stream
structure T = Terminal

(* Error reporting *)
val quiet = ref false
fun error pos msg = if !quiet then () else ErrorMsg.error (PS.ext pos) msg

(* Prohibit annotations, for L1-5 language fragments *)
val lexAnnos = ref true

val maxcol = 80
val warnings = ref true
fun warn pos msg = if !warnings
                   then ErrorMsg.warn (PS.ext pos) msg
                   else ()
fun toolong () = ("line too long: " ^ Int.toString (PS.linewidth()) ^ " > " ^ Int.toString maxcol)

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
         ("illegal escape sequence '\\" ^ Char.toString c ^ "'")

(* Grab a complete string *)
fun lex_string (pos, charstream, string) : int * char M.stream * string option = 
   case M.force charstream of
      M.Nil => (pos, charstream, NONE) 
      before error (pos, pos) "string constant not terminated"
    | M.Cons (#"\"", cs) => 
      let
         fun collect_rev (chars, str) = 
           case chars of 
              [] => SOME (String.implode str)
            | (NONE :: _) => NONE
            | (SOME c :: cs) => collect_rev (cs, c :: str)
      in (pos+1, cs, collect_rev (string, [])) end
    | M.Cons (#"\n", cs) => 
      (PS.newline pos
       ; error (pos, pos+1) "illegal newline in string; use '\\n'"
       ; lex_string (pos+1, cs, NONE :: string))
    | M.Cons (#"\\", cs) => 
      (case M.force cs of 
          M.Nil => lex_string (pos+1, cs, NONE :: string)
        | M.Cons (c, cs) => lex_string (pos+2, cs, special_char c pos :: string))
    | M.Cons (c, cs) => lex_string (pos+1, cs, SOME c :: string)

(* "Normal" lexing *)
fun lex_code (pos, charstream, code_state) = 
   let
      val cs = charstream
      val s = CODE code_state
      fun run_cond cond (n, s, cs) = 
         case M.force cs of
            M.Nil => (String.implode (rev s), n, cs)
          | M.Cons (c, cs') =>
            if cond c
            then run_cond cond (n+1, c :: s, cs')
            else (String.implode (rev s), n, cs)
      val run_alpha = run_cond (fn c => Char.isAlphaNum c orelse c = #"_")
      val run_number = run_cond Char.isDigit
      val run_hex = run_cond Char.isHexDigit
   in
      case M.force charstream of 
       (* End of file *)
         M.Nil => (T.EOF, pos, pos, charstream, s)

       (* Whitespace *)
       | M.Cons (#" ", cs) => lex_code (pos+1, cs, code_state)
       | M.Cons (#"\t", cs) => ( warn (pos, pos+1) ("replace tab character by spaces")
                               ; lex_code (pos+1, cs, code_state) )
       | M.Cons (#"\011", cs) => lex_code (pos+1, cs, code_state)
       | M.Cons (#"\012", cs) => lex_code (pos+1, cs, code_state)
       | M.Cons (#"\r", cs) => lex_code (pos+1, cs, code_state)
       | M.Cons (#"\n", cs) => 
         (PS.newline pos
          ; if !warnings andalso PS.linewidth() > maxcol
            then warn (pos-PS.linewidth(), pos) (toolong ())
            else ()
          ; case code_state of
               ANNO_LINE => (T.ANNO_END,    pos, pos+1, cs, CODE NORMAL)
             | _ => lex_code (pos+1, cs, code_state))

       (* Separators *)
       | M.Cons (#"{", cs) => (T.LBRACE,       pos, pos+1, cs, s)
       | M.Cons (#"}", cs) => (T.RBRACE,       pos, pos+1, cs, s)
       | M.Cons (#"(", cs) => (T.LPAREN,       pos, pos+1, cs, s)
       | M.Cons (#")", cs) => (T.RPAREN,       pos, pos+1, cs, s)
       | M.Cons (#"[", cs) => (T.LBRACKET,     pos, pos+1, cs, s)
       | M.Cons (#"]", cs) => (T.RBRACKET,     pos, pos+1, cs, s)
       | M.Cons (#",", cs) => (T.COMMA,        pos, pos+1, cs, s)
       | M.Cons (#":", cs) => (T.COLON,        pos, pos+1, cs, s)
       | M.Cons (#";", cs) => (T.SEMI,         pos, pos+1, cs, s)
       | M.Cons (#".", cs) => (T.DOT,          pos, pos+1, cs, s)
       | M.Cons (#"~", cs) => (T.TILDE,        pos, pos+1, cs, s)
       | M.Cons (#"?", cs) => (T.QUEST,        pos, pos+1, cs, s)

       (* Math *)
       | M.Cons (#"=", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.EQEQ,     pos, pos+2, cs, s)
           | _ =>                 (T.EQ,       pos, pos+1, cs, s))
       | M.Cons (#"+", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.PLUSEQ,   pos, pos+2, cs, s)
           | M.Cons (#"+", cs) => (T.PLUSPLUS, pos, pos+2, cs, s)
           | _ =>                 (T.PLUS,     pos, pos+1, cs, s))
       | M.Cons (#"-", cs) => 
         (case M.force cs of 
             M.Cons (#"=", cs) => (T.MINUSEQ,    pos, pos+2, cs, s)
           | M.Cons (#"-", cs) => (T.MINUSMINUS, pos, pos+2, cs, s)
           | M.Cons (#">", cs) => (T.ARROW,      pos, pos+2, cs, s)
           | _ =>                 (T.MINUS,      pos, pos+1, cs, s))
       | M.Cons (#"*", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.STAREQ, pos, pos+2, cs, s)
           | _ =>                 (T.STAR,   pos, pos+1, cs, s))
       | M.Cons (#"#", cs) => 
         if (code_state <> NORMAL)
         then (T.LEX_ERROR, pos, pos+1, cs, s)
              before error (pos, pos+1) "#pragma in annotation"
         else lex_pragma (pos+1, cs, [ #"#" ])
       | M.Cons (#"/", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.SLASHEQ,   pos, pos+2, cs, s)
           | M.Cons (#"/", cs) => 
             (case M.force cs of
                M.Cons (#"@", cs) => 
                (case (code_state,!lexAnnos) of
                    (NORMAL,true) => (T.ANNO_BEGIN, pos, pos+3, cs, CODE ANNO_LINE)
                  | (NORMAL,false) => lex_comment_line (pos+3, cs, code_state)
                  (*
                    (T.LEX_ERROR, pos, pos+3, cs, s)
                    before error (pos, pos+3) "annotations not allowed in language fragment"
                  *)
                  | _ =>      (T.LEX_ERROR,  pos, pos+3, cs, s)
                    before error (pos, pos+3) "no nested annotations")
              | _ => lex_comment_line (pos+2, cs, code_state))
           | M.Cons (#"*", cs) => 
             (case M.force cs of
                M.Cons (#"@", cs) =>
                (case (code_state,!lexAnnos) of
                    (NORMAL,true) => (T.ANNO_BEGIN, pos, pos+3, cs, CODE ANNO)
                  | (NORMAL,false) => lex_comment (pos+3, cs, 1, code_state)
                  (*
                  | (_,false) => (T.LEX_ERROR, pos, pos+3, cs, s)
                    before error (pos, pos+3) "annotations not allowed in language fragment"
                  *)
                  | _ =>      (T.LEX_ERROR,  pos, pos+3, cs, s)
                    before error (pos, pos+3) "no nested annotations")
              | _ => lex_comment (pos+2, cs, 1, code_state))
           | _ => (T.SLASH, pos, pos+1, cs, s))
       | M.Cons (#"%", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.PERCENTEQ,  pos, pos+2, cs, s)
           | _ =>                 (T.PERCENT,    pos, pos+1, cs, s))
       | M.Cons (#"&", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.AMPEQ,      pos, pos+2, cs, s)
           | M.Cons (#"&", cs) => (T.AMPAMP,     pos, pos+2, cs, s)
           | _ =>                 (T.AMP,        pos, pos+1, cs, s))
       | M.Cons (#"^", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.CARETEQ,    pos, pos+2, cs, s)
           | _ =>                 (T.CARET,      pos, pos+1, cs, s))
       | M.Cons (#"|", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.BAREQ,      pos, pos+2, cs, s)
           | M.Cons (#"|", cs) => (T.BARBAR,     pos, pos+2, cs, s)
           | _ =>                 (T.BAR,        pos, pos+1, cs, s))
       | M.Cons (#"!", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.EXCLEQ,     pos, pos+2, cs, s)
           | _ =>                 (T.EXCL,       pos, pos+1, cs, s))
       | M.Cons (#"<", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) => (T.LEQ,        pos, pos+2, cs, s)
           | M.Cons (#"<", cs) => 
             (case M.force cs of
                 M.Cons (#"=", cs) => (T.LLEQ,   pos, pos+3, cs, s)
               | _ =>                 (T.LL,     pos, pos+2, cs, s))
           | _ =>                     (T.LESS,   pos, pos+1, cs, s))
       | M.Cons (#">", cs) => 
         (case M.force cs of
             M.Cons (#"=", cs) =>     (T.GEQ,    pos, pos+2, cs, s)
           | M.Cons (#">", cs) => 
             (case M.force cs of
                 M.Cons (#"=", cs) => (T.GGEQ,    pos, pos+3, cs, s)
               | _ =>                 (T.GG,      pos, pos+2, cs, s))
           | _ =>                     (T.GREATER, pos, pos+1, cs, s))

       (* The curious case of @ - whitespace, but only in annotations *)
       | M.Cons (#"@", cs) =>
         let val end_anno = 
            case M.force cs of 
               M.Cons (#"*", cs) => 
               (case M.force cs of M.Cons (#"/", cs) => SOME cs | _ => NONE)
             | _ => NONE
         in 
            case end_anno of
               NONE => 
               (if code_state <> NORMAL then lex_code (pos+1, cs, code_state)
                else ((T.LEX_ERROR, pos, pos+1, cs, s)
                before error (pos, pos)
                      "character '@' is illegal outside of an annotation"))
             | SOME cs => 
               (if code_state = ANNO 
                then (T.ANNO_END, pos, pos+3, cs, CODE NORMAL)
                else ((T.LEX_ERROR,   pos, pos+3, cs, s)
                      before error (pos, pos+3)
		             "token '@*/' outside delimited annotation"))
         end

       (* Escaped identifiers *)
       | M.Cons (#"\\", cs) => 
         (case run_alpha (1, [], cs) of
             ("result", n, cs) => (T.BS_RESULT, pos, pos+n, cs, s)
           | ("length", n, cs) => (T.BS_LENGTH, pos, pos+n, cs, s)
           | ("hastag", n, cs) => (T.BS_HASTAG, pos, pos+n, cs, s)
           | (bs, n, cs) =>       (T.LEX_ERROR, pos, pos+n, cs, s)
             before error (pos, pos)
                ("illegal escaped identifier: '\\" ^ bs ^ "'"))

       (* Char constants *)
       | M.Cons (#"'", cs) =>
         let 
            val (c, cs, pos') =
            case M.force cs of 
               M.Nil => (NONE, cs, pos+1)
               before error (pos, pos+1) "incomplete char constant" 
             | M.Cons (#"\\", cs) => 
               (case M.force cs of 
                   M.Nil => (NONE, cs, pos+2)
                   before error (pos, pos+1) "incomplete char constant"
                 | M.Cons (c, cs) => 
                   let val s = "\\" ^ str c 
                   in (SOME s, cs, pos+3) end)
             | M.Cons (#"\n", cs) => (NONE, cs, pos+2)
               before error (pos, pos+2) "illegal newline in char; use '\\n'"
             | M.Cons (c, cs) => 
               if Char.isPrint c 
               then (SOME (str c), cs, pos+2)
               else ((NONE, cs, pos+2)
                     before error (pos, pos+2) "non-printable character")
         in 
            case (c, M.force cs) of 
               (SOME c, M.Cons (#"'", cs)) => (T.CHRLIT(c), pos, pos'+1, cs, s)
             | (_, M.Nil) =>                  (T.LEX_ERROR, pos, pos', cs, s)
               before error (pos, pos')
               "incomplete char constant: expected ''' but found end of input"
             | (NONE, M.Cons (#"'", cs)) =>   (T.LEX_ERROR, pos, pos'+1, cs, s) (* msg? *)
             | (NONE, _) =>                   (T.LEX_ERROR, pos, pos', cs, s)   (* msg? *)
             | (SOME _, M.Cons (c, _)) =>     (T.LEX_ERROR, pos, pos', cs, s) 
               before error (pos, pos'+1)
               ("bad char constant: expected ''' but found '" ^ Char.toCString c ^ "'")
         end

       (* String constants *)
       | M.Cons (#"\"", cs) => 
         let val (pos', cs, string) = lex_string (pos+1, cs, []) in
            case string of 
               NONE =>     (T.LEX_ERROR,    pos, pos', cs, s)
             | SOME str => (T.STRLIT(str),  pos, pos', cs, s)
         end

       (* Some decimal constants; all hexidecimal constants *)
       | M.Cons (#"0", cs') =>
         (case M.force cs' of
             M.Cons (#"x", cs) => 
             let val (num, n, cs) = run_hex (2, [], cs)
             in (T.HEXNUM(num), pos, pos+n, cs, s) end
           | M.Cons (#"X", cs) => 
             let val (num, n, cs) = run_hex (2, [], cs)
             in (T.HEXNUM(num), pos, pos+n, cs, s) end
           | M.Cons (c, cs'') => 
             if Char.isDigit c 
             then (T.LEX_ERROR, pos, pos+2, cs'', s)
                  before error (pos, pos+2)
                  "non-zero integer constants cannot start with '0'"
             else (T.DECNUM("0"), pos, pos+1, cs', s)
           | M.Nil => (T.DECNUM("0"), pos, pos+1, cs', s))

       (* Keywords, numbers, and identifiers *)
       | M.Cons (c, cs') => 
         (if Char.isAlpha c orelse c = #"_"
          then 
          (case run_alpha (0, [], charstream) of
              ("struct",  n, cs) =>     (T.STRUCT, pos, pos+n, cs, s)
            | ("typedef", n, cs) =>     (T.TYPEDEF, pos, pos+n, cs, s)
            | ("int",     n, cs) =>     (T.INT, pos, pos+n, cs, s)
            | ("bool", n, cs) =>        (T.BOOL, pos, pos+n, cs, s)
            | ("char", n, cs) =>        (T.CHAR, pos, pos+n, cs, s)
            | ("string", n, cs) =>      (T.STRING, pos, pos+n, cs, s)
            | ("void", n, cs) =>        (T.VOID, pos, pos+n, cs, s)
            | ("if", n, cs) =>          (T.IF, pos, pos+n, cs, s)
            | ("else", n, cs) =>        (T.ELSE, pos, pos+n, cs, s)
            | ("for", n, cs) =>         (T.FOR, pos, pos+n, cs, s)
            | ("while", n, cs) =>       (T.WHILE, pos, pos+n, cs, s)
            | ("continue", n, cs) =>    (T.CONTINUE, pos, pos+n, cs, s)
            | ("break", n, cs) =>       (T.BREAK, pos, pos+n, cs, s)
            | ("return", n, cs) =>      (T.RETURN, pos, pos+n, cs, s)
            | ("true", n, cs) =>        (T.TRUE, pos, pos+n, cs, s)
            | ("false", n, cs) =>       (T.FALSE, pos, pos+n, cs, s)
            | ("NULL", n, cs) =>        (T.NULL, pos, pos+n, cs, s)
            | ("alloc", n, cs) =>       (T.ALLOC, pos, pos+n, cs, s)
            | ("alloc_array", n, cs) => (T.ALLOC_ARRAY, pos, pos+n, cs, s)
            | ("requires", n, cs) =>    (T.REQUIRES, pos, pos+n, cs, s)
            | ("ensures", n, cs) =>     (T.ENSURES, pos, pos+n, cs, s)
            | ("loop_invariant", n, cs) => (T.LOOP_INVARIANT, pos, pos+n, cs, s)
            | ("assert", n, cs) =>      (T.ASSERT, pos, pos+n, cs, s)
            | ("error", n, cs) =>       (T.ERROR, pos, pos+n, cs, s)
            | (ident, n, cs) =>         (T.IDENT(ident), pos, pos+n, cs, s))
          (* Numerical constants *)
          else if Char.isDigit c 
          then 
          (let val (num, n, cs) = run_number (0, [], charstream)
           in (T.DECNUM(num), pos, pos+n, cs, s) end)
          else (T.LEX_ERROR, pos, pos+1, cs', s)
             before error (pos, pos)
             ("illegal character: '" ^ Char.toString c ^ "'"))
   end

and lex_comment (pos, charstream, depth, prev) = 
   case M.force charstream of
      M.Nil => (T.EOF, pos, pos, charstream, COMMENT (depth, prev))
    | M.Cons (#"\n", cs) => 
      (PS.newline pos
       ; if !warnings andalso PS.linewidth() > maxcol
         then warn (pos-PS.linewidth(), pos) (toolong ())
         else ()
       ; case prev of
            ANNO_LINE => error (pos, pos+1)
            "end of delimited comment in single-line annotation"
          | _ => ()
       ; lex_comment (pos+1, cs, depth, prev))
    | M.Cons (#"/", cs) =>
      (case M.force cs of
          M.Cons (#"*", cs) => lex_comment (pos+2, cs, depth+1, prev)
        | _ => lex_comment (pos+1, cs, depth, prev))
    | M.Cons (#"*", cs) =>
      (case M.force cs of
          M.Cons (#"/", cs) => 
          (if depth <= 1 then lex_code (pos+2, cs, prev)
           else lex_comment (pos+2, cs, depth-1, prev))
        | _ => lex_comment (pos+1, cs, depth, prev))
    | M.Cons (_, cs) => lex_comment (pos+1, cs, depth, prev)

and lex_escape_pragma (pos, charstream, pragma) = 
   case M.force charstream of
      M.Nil => (T.EOF, pos, pos, charstream, ESCAPE_PRAGMA pragma)
    | M.Cons (#"\n", cs) => 
      ( PS.newline pos
      ; lex_pragma (pos+1, cs, #"\n" :: pragma) )
    | M.Cons (c, cs) => lex_pragma (pos+1, cs, c :: pragma)

and lex_pragma (pos, charstream, pragma) = 
   case M.force charstream of
      M.Nil => (T.EOF, pos, pos, charstream, NORMAL_PRAGMA pragma)
    | M.Cons (#"\\", cs) => lex_escape_pragma (pos+1, cs, #"\\" :: pragma)
    | M.Cons (#"\n", cs) => 
      let val old_pos = pos - length pragma in
          PS.newline pos
        ; if !warnings andalso PS.linewidth() > maxcol
          then warn (pos-PS.linewidth(), pos) (toolong())
          else ()
        ; (T.PRAGMA(implode (rev pragma)), old_pos, pos+1, cs, CODE NORMAL) 
      end
    | M.Cons (c, cs) => lex_pragma (pos+1, cs, c :: pragma)

and lex_comment_line (pos, charstream, prev) = 
   case M.force charstream of
      M.Nil => (T.EOF, pos, pos, charstream, COMMENT_LINE prev)
    | M.Cons (#"\n", cs) => 
      ( PS.newline pos
      ; if !warnings andalso PS.linewidth() > maxcol
        then warn (pos-PS.linewidth(), pos) (toolong())
        else ()
      ; case prev of
            ANNO_LINE => (T.ANNO_END, pos, pos+1, cs, CODE NORMAL)
          | _ => lex_code (pos+1, cs, prev))
    | M.Cons (_, cs) => lex_comment_line (pos+1, cs, prev)

(* Interface functions follow *)

(* lex (pos, charstream, state)
 * continues to lex from "charstream", assuming position "pos"
 * and lexer state "state".  This generality is necessary for
 * the interaction top-level loop (coin)
 *)
type lexanswer = T.terminal * int * int * char Stream.stream * state

fun lex (pos, charstream, state) : lexanswer =
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
         else fn () => M.Cons (String.sub (str, i), use_buf (str, len, i+1))

      and refill_buf () =
          let
              val memo = ref (fn () => raise Match)
              fun read () =
                 let val ans = 
                    case source 1024 of 
                       "" => M.Nil
                     | s => M.Cons (String.sub (s, 0), use_buf (s, size s, 1))
                 in memo := (fn () => ans); ans end
          in memo := read; (fn () => (!memo) ()) end
   in refill_buf () end

fun str_stream str = 
    let val r = ref false
    in buffered_stream (fn _ => if !r then "" else (r := true; str)) end

type lexresult = T.terminal * (int * int)

fun lexer (pos, charstream, state) =
    let val (tok, left_pos, right_pos, new_stream, new_state) = lex (pos, charstream, state)
	fun check_eof T.EOF state = 
	    (case state of 
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
		  ("#pragma not terminated by newline at end of file"))
          | check_eof t state = ()
  in (* does the recursive call make sense if we are T.EOF ?  Or should it be M.Nil? *)
      check_eof tok new_state
    ; M.Cons ((tok, (left_pos, right_pos)), fn () => lexer (right_pos, new_stream, new_state))
  end

(* The starting value is 2 because of a miracle [Issue #42] - rjs 12/29/2012 
 * See also coin/coin.sml *)
fun makeLexer source = fn () => lexer (2, buffered_stream source, CODE NORMAL)

fun lineLexer (cs, pos, lex_state) =
let
   fun collect_toks (pos, cs, lex_state) accum =
      case lex (pos, cs, lex_state) of 
         (Terminal.EOF, pos, pos', _, lex_state') =>
           ( Stream.fromList (rev ((Terminal.EOL, (pos, pos')) :: accum))
           , pos'
           , lex_state')
       | (tok, left, right, cs', lex_state') =>
            collect_toks (right, cs', lex_state') 
               ((tok, (left, right)) :: accum)
in
   collect_toks (pos, cs, lex_state) []
end

end
