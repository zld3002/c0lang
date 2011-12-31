signature PARSE_PRAGMA =
sig
    val parse_use : string -> Mark.ext option -> Ast.pragma
    val parse_pragma : string -> Mark.ext option -> Ast.pragma
end

structure ParsePragma :> PARSE_PRAGMA =
struct

  fun use_reader ext char_reader cs =
      (case char_reader cs
	of SOME(#"\"", cs') => filename_reader nil ext char_reader cs'
	 | SOME(#"<", cs') => libname_reader nil ext char_reader cs'
         | SOME(c, cs') =>
	     if Char.isSpace(c)
	     then use_reader ext char_reader cs'
	     else  ( ErrorMsg.error ext ("#use pragma not followed by \"file\" or <lib>") ;
		     raise ErrorMsg.Error )
         | NONE => ( ErrorMsg.error ext ("#use pragma not followed by \"file\" or <lib>") ;
		     raise ErrorMsg.Error ))
  and filename_reader chars ext char_reader cs =
      (case char_reader cs
	of SOME(#"\"", cs') => whitespace_reader (Ast.UseFile (String.implode (List.rev chars), NONE))
						 ext char_reader cs'
	 | SOME(c, cs') =>
	   if not(Char.isPrint(c))
	   then ( ErrorMsg.error ext ("illegal character " ^ Char.toCString(c) ^ " in filename") ;
		  raise ErrorMsg.Error )
	   else filename_reader (c::chars) ext char_reader cs'
         | NONE => ( ErrorMsg.error ext ("unclosed file name") ;
		     raise ErrorMsg.Error ))
  and libname_reader chars ext char_reader cs =
      (case char_reader cs
	of SOME(#">", cs') => whitespace_reader (Ast.UseLib (String.implode(List.rev chars), NONE))
						ext char_reader cs'
         | SOME(c, cs') =>
	   if not(Char.isPrint(c))
	   then ( ErrorMsg.error ext ("illegal character " ^ Char.toCString(c) ^ " in filename") ;
		  raise ErrorMsg.Error )
           else libname_reader (c::chars) ext char_reader cs'
	 | NONE => ( ErrorMsg.error ext ("unclosed library name") ;
		     raise ErrorMsg.Error ))
  and whitespace_reader name ext char_reader cs =
      (case char_reader cs
	of SOME(c, cs') =>
	   if not(Char.isSpace(c))
	   then ( ErrorMsg.error ext ("unexpected character " ^ Char.toCString(c) ^ " after file or library name") ;
		  raise ErrorMsg.Error )
	   else whitespace_reader name ext char_reader cs'
	 | NONE => SOME(name, cs))

  and any_reader pragma chars ext char_reader cs =
      (case char_reader cs
	of SOME(c, cs') => any_reader pragma (c::chars) ext char_reader cs'
	 | NONE => SOME(Ast.Raw(pragma, String.implode(List.rev chars)), cs))

  fun id_reader' chars ext char_reader cs =
      (case char_reader cs
	of SOME(c, cs') =>
	   if Char.isAlphaNum(c) orelse c = #"_"
	   then id_reader' (c::chars) ext char_reader cs'
	   else let val pragma = String.implode(List.rev chars)
		in
		    case pragma
		     of "#use" => use_reader ext char_reader cs'
		      | _ => any_reader pragma nil ext char_reader cs'
		end
	 | NONE => SOME(Ast.Raw(String.implode(List.rev chars), ""), cs))

  fun id_reader chars ext char_reader cs =
      (case char_reader cs
	of SOME(c, cs') =>
	   if Char.isAlpha(c) orelse c = #"_"
	   then id_reader' (c::chars) ext char_reader cs'
	   else any_reader (String.implode(List.rev chars)) nil ext char_reader cs'
         | NONE => SOME(Ast.Raw(String.implode(List.rev chars), ""), cs))
	   
  fun pragma_reader ext char_reader cs =
      (case char_reader cs
	of SOME(#"#", cs') => id_reader [#"#"] ext char_reader cs')

  fun parse_use line ext =
      valOf (StringCvt.scanString (use_reader ext) line)

  fun parse_pragma line ext =
      valOf (StringCvt.scanString (pragma_reader ext) line)

end
