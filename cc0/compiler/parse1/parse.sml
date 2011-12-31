(* C0 Compiler
 * Parsing
 * Frank Pfenning <fp@cs.cmu.edu>
 *
 * Glueing together the pieces produced by ML-Lex and ML-Yacc
 *)

signature PARSE =
sig
  (* parse filename process_library = ast
   * will raise ErrorMsg.Error in case of lexing or parsing error
   * process_library is called on #use <lib>
   *)
  val parse : string
	      -> (string -> Ast.program)  (* processing #use <lib> *)
	      -> (string -> string -> Ast.program) (* procession #use "file" *)
	      -> Ast.program
end

structure Parse :> PARSE =
struct 

  structure C0LrVals = C0LrValsFn (structure Token = LrParser.Token)
  structure C0Lex = C0LexFn (structure Tokens = C0LrVals.Tokens)
  structure C0Parse = Join (structure ParserData = C0LrVals.ParserData
                            structure Lex = C0Lex
                            structure LrParser = LrParser)

  (* Main parsing function *)
  fun parse filename process_library process_file =
      SafeIO.withOpenIn filename (fn instream =>
        let 
	  (* val _ = ErrorMsg.reset() *) (* now in top.sml; no errors, no messages so far *)
	  val _ = ParseState.pushfile filename (* start at position 0 in filename *)
	  (* val _ = Typetab.reset() *) (* reset known type names, now in top/top.sml *)
	  fun parseerror (s, p1, p2) = ErrorMsg.error (ParseState.ext (p1,p2)) s
	  val dummyEOF = C0LrVals.Tokens.EOF(0,0)
	  val dummySEMI = C0LrVals.Tokens.SEMI(0,0)
	  val lexer = LrParser.Stream.streamify
			  (C0Lex.makeLexer (fn _ => TextIO.input instream))
	  (* 0 = no error correction, 15 = reasonable lookahead for correction *)
          (* cannot use anything > 0 because processing typedefs changes future lexing *)
          fun collect (lexer, accum) =
	        collect'(C0Parse.parse(0, lexer, parseerror, ()), accum)
	  and collect' ((Ast.Pragma(Ast.Raw("#use", pline), ext), lexer), accum) =
	      (* need to process #use right away; even next token might be affected! *)
	      let val p = case ParsePragma.parse_use pline ext
			    of Ast.UseLib(libname, NONE) =>
			       Ast.UseLib(libname, SOME(process_library libname))
			     | Ast.UseFile(usefile, NONE) => 
			       Ast.UseFile(usefile, SOME(process_file filename usefile))
	      in
		  collect'''(C0Parse.Stream.get lexer, lexer, Ast.Pragma(p, ext)::accum)
	      end
	    | collect' ((result, lexer), accum) =
	        collect''(C0Parse.Stream.get lexer, lexer, result::accum)
	  and collect'' ((nextToken, lexer'), lexer, accum as (Ast.TypeDef(id,tp,ext)::_)) =
	      ( Typetab.bind(id, (tp,ext)) ;
		if C0Parse.sameToken(nextToken, dummySEMI)
		then (* was : collect(lexer', accum) which did not allow file to end in typedef *)
		    collect'''(C0Parse.Stream.get lexer', lexer', accum)
		else ( ErrorMsg.error ext ("typedef not followed by `;'") ;
		       collect(lexer, accum) )
	      )
            | collect'' ((nextToken, lexer'), lexer, accum) =
	      if C0Parse.sameToken(nextToken, dummyEOF)
		 then List.rev accum
	      else collect(lexer, accum)
	  and collect''' ((nextToken, lexer'), lexer, accum) =
	      if C0Parse.sameToken(nextToken, dummyEOF)
		 then List.rev accum
	      else collect(lexer, accum)
          (* allow empty file *)
	  val absyn = collect'' (C0Parse.Stream.get lexer, lexer, nil)
          val _ = if !ErrorMsg.anyErrors
		  then raise ErrorMsg.Error
		  else ()
	  val _ = ParseState.popfile()
	in
	  absyn
	end)
      handle (* C0Lex.LexError => ( ErrorMsg.error NONE "lexer error" ;
			       raise ErrorMsg.Error )
           | *)
	     Fail(msg) => ( ErrorMsg.error NONE ("lexer error: " ^ msg) ;
			    raise ErrorMsg.Error )
	   | LrParser.ParseError => raise ErrorMsg.Error (* always preceded by msg *)
           | e as IO.Io _ => ( ErrorMsg.error NONE (exnMessage e);
                               raise ErrorMsg.Error )

end
