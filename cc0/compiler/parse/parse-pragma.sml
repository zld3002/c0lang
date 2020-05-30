(* C0 Compiler
 * Parsing pragmas #<pragma_name> <line>\n
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature PARSE_PRAGMA =
sig
    val parse_use : string -> Mark.ext option -> Ast.pragma
    val parse_pragma : string -> Mark.ext option -> Ast.pragma
end

structure ParsePragma :> PARSE_PRAGMA =
struct

  (* We use the StringCvt types and functions for parsing pragmas.
   * See http://www.standardml.org/Basis/string-cvt.html#STRING_CVT:SIG:SPEC
   * type StringCvt.cs
   * type ('a,'b) StringCvt.reader = 'b -> ('a * 'b) option
   *
   * Below we use notational conventions
   * cs : StringCvt.cs is a character stream
   * char_reader : (char, StringCvt.cs) StringCvt.reader is a character reader
   * ext : Mark.ext option is the extent of the input line in the source file
   *)

  (* whitespace_reader pragma ext char_reader cs = SOME(pragma, empty_cs)
   * consumes trailing whitespace in character stream cs, raises ErrorMsg.Error if ill-formed *)
  fun whitespace_reader pragma ext char_reader cs =
      (case char_reader cs
        of SOME(c, cs') =>
           if not(Char.isSpace(c))
           then ( ErrorMsg.error ext ("unexpected character " ^ C0Char.toC0String(c) ^ " after file or library name")
                ; raise ErrorMsg.Error )
           else whitespace_reader pragma ext char_reader cs'
         | NONE => SOME(pragma, cs))

  (* libname_reader chars ext char_reader cs = SOME(pragma, empty_cs)
   * reads <libname> with accumulator chars, raises ErrorMsg.Error if ill-formed *)
  fun libname_reader chars ext char_reader cs =
      (case char_reader cs
        of SOME(#">", cs') => whitespace_reader (Ast.UseLib (String.implode(List.rev chars), NONE))
                                                ext char_reader cs'
         | SOME(c, cs') =>
           if not(Char.isPrint(c))
           then ( ErrorMsg.error ext ("illegal character " ^ C0Char.toC0String(c) ^ " in filename")
                ; raise ErrorMsg.Error )
           else libname_reader (c::chars) ext char_reader cs'
         | NONE => ( ErrorMsg.error ext ("unclosed library name")
                   ; raise ErrorMsg.Error ))

  (* filename_reader chars ext char_reader cs : Ast.pragma option
   * reads "filename" with accumulator chars, raises ErrorMsg.Error if ill-formed *)
  fun filename_reader chars ext char_reader cs =
      (case char_reader cs
        of SOME(#"\"", cs') => whitespace_reader (Ast.UseFile (String.implode (List.rev chars), NONE))
                                                 ext char_reader cs'
         | SOME(c, cs') =>
           if not(Char.isPrint(c))
           then ( ErrorMsg.error ext ("illegal character " ^ C0Char.toC0String(c) ^ " in filename")
                ; raise ErrorMsg.Error )
           else filename_reader (c::chars) ext char_reader cs'
         | NONE => ( ErrorMsg.error ext ("unclosed file name")
                   ; raise ErrorMsg.Error ))

  (* use_reader ext char_reader cs = SOME(pragma, empty_cs)
   * reads "file" or <lib> following #use, raises ErrorMsg.Error if ill-formed *)
  fun use_reader ext char_reader cs =
      (case char_reader cs
        of SOME(#"\"", cs') => filename_reader nil ext char_reader cs'
         | SOME(#"<", cs') => libname_reader nil ext char_reader cs'
         | SOME(c, cs') =>
             if Char.isSpace(c)
             then use_reader ext char_reader cs'
             else  ( ErrorMsg.error ext ("#use pragma not followed by \"file\" or <lib>")
                   ; raise ErrorMsg.Error )
         | NONE => ( ErrorMsg.error ext ("#use pragma not followed by \"file\" or <lib>")
                   ; raise ErrorMsg.Error ))

  (* any_reader pragma_name chars ext char_reader cs = SOME(pragma, empty_cs)
   * reads remainder of line following pragma name *)
  and any_reader pragma_name chars ext char_reader cs =
      (case char_reader cs
        of SOME(c, cs') => any_reader pragma_name (c::chars) ext char_reader cs'
         | NONE => SOME(Ast.Raw(pragma_name, String.implode(List.rev chars)), cs))

  (* id_reader' chars ext char_reader cs = SOME(pragma, empty_cs)
   * reads chars 2-n of pragma name and continues based on pragma name *)
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

  (* id_reader chars ext char_reader cs : Ast.pragma option
   * reads first character of pragma name following '#' and continues *)
  fun id_reader chars ext char_reader cs =
      (case char_reader cs
        of SOME(c, cs') =>
           if Char.isAlpha(c) orelse c = #"_"
           then id_reader' (c::chars) ext char_reader cs'
           else any_reader (String.implode(List.rev chars)) nil ext char_reader cs'
         | NONE => SOME(Ast.Raw(String.implode(List.rev chars), ""), cs))
           
  (* pragma_reader ext char_reader cs : Ast.pragma option = pragma
   * reads leading '#' (which must be there) and continues *)
  fun pragma_reader ext char_reader cs =
      (case char_reader cs
        of SOME(#"#", cs') => id_reader [#"#"] ext char_reader cs')

  (* parse_use line ext : Ast.pragma option
   * is like parse_pragma, but assumes #use has already been parsed *)
  fun parse_use line ext =
      valOf (StringCvt.scanString (use_reader ext) line)

  (* parse_pragma line ext = A.UseLib (libname, NONE)   for #use <libname>
   *                       = A.UseFile (filename, NONE) for #use "filename"
   *                       = A.Raw (pid, rest)          for #pid rest (if not #use)
   * raises ErrorMsg.Error on syntax error for #use pragmas
   * line must start with '#'
   *)
  fun parse_pragma line ext =
      valOf (StringCvt.scanString (pragma_reader ext) line)

end
