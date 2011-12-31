signature PARSER =
sig
    (* Parse source file *)
    val parse : string -> C0.program * Mark.ext Vector.vector
    (* Parse source string *)
    val parse_string : string -> C0.exp option
end

structure Parser :> PARSER =
struct

structure C0LrVals = C0LrValsFn (structure Token = LrParser.Token)
structure C0Lex = C0LexFn (structure Tokens = C0LrVals.Tokens)
structure C0Parse = Join (structure ParserData = C0LrVals.ParserData
structure Lex = C0Lex
structure LrParser = LrParser)


fun parse filename =
    SafeIO.withOpenIn filename 
		      (fn instream =>
			  let
			      val _ = ParseState.setfile filename
			      val lexer = LrParser.Stream.streamify
					      (C0Lex.makeLexer (fn _ => TextIO.input instream))
			      fun parseerror (s, p1, p2) = ErrorMsg.error (ParseState.ext (p1,p2)) s
			      val _ = ErrorMsg.anyErrors := false
			      val (absyn, _) = C0Parse.parse(0, lexer, parseerror, ()) (*0 = no lookahead for correction*)
			      val _ = if !ErrorMsg.anyErrors
				      then raise ErrorMsg.Error
				      else ()
			  in
			      absyn
			  end)

fun parse_string s = 
    let
	val _ = ParseState.setfile "stdin"
	val gaveString = ref false
	val input = TextIO.openString ("void _() {void _ =" ^ s ^ ";}")
	val lexer = LrParser.Stream.streamify
			(C0Lex.makeLexer (fn _ => TextIO.input input))
	fun parseerror (msg, p1, p2) = () (* No error messages from parser *)
	val _ = ErrorMsg.anyErrors := false
	val (absyn, _) = C0Parse.parse(0, lexer, parseerror, ()) (*0 = no lookahead for correction*)
	val result = (case #1 absyn 
		       of [C0.DeclFunDef
			       ((C0.TyUnit,"_",[]),
				[C0.Decl (C0.TyUnit,C0.Normal "_", EXP,_)])
			  ] => EXP
			| _ => NONE
		     )
    in
	if !ErrorMsg.anyErrors
	then NONE
	else result
    end
    handle _ => NONE
end
