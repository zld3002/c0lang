(* Adapted from SML/NJ implementation of Char *)

signature C0CHAR =
sig
    val fromC0String : string -> char option
    val toC0String : char -> string
end

structure C0Char :> C0CHAR =
struct
    (* scanning function for C-style escape sequences *)
    (* val scanC0 : (char, 'a) StringCvt.reader -> (char, 'a) StringCvt.reader *)
    (* internal scanning function for C-style escape sequences in C0 *)
    fun scanC0 getc strm =
        let
            fun scan (NONE) = NONE
              | scan (SOME(#"\\", strm')) =
                (case getc strm'
                  of NONE => NONE
                   | (SOME(#"a", strm'')) => SOME(#"\a", strm'')
                   | (SOME(#"b", strm'')) => SOME(#"\b", strm'')
                   | (SOME(#"t", strm'')) => SOME(#"\t", strm'')
                   | (SOME(#"n", strm'')) => SOME(#"\n", strm'')
                   | (SOME(#"v", strm'')) => SOME(#"\v", strm'')
                   | (SOME(#"f", strm'')) => SOME(#"\f", strm'')
                   | (SOME(#"r", strm'')) => SOME(#"\r", strm'')
                   | (SOME(#"\\", strm'')) => SOME(#"\\", strm'')
                   | (SOME(#"\"", strm'')) => SOME(#"\"", strm'')
                   | (SOME(#"'", strm'')) => SOME(#"'", strm'')
                   | (SOME(#"0", strm'')) => SOME(Char.chr(0), strm'')
                   (* | (SOME(#"?", strm'')) => SOME(#"?", strm'') *)
                   (* | (SOME(#"x", strm'')) => (* hex escape code *)
                            chkDigits StringCvt.HEX
                              (scanDigits isHexDigit getc ~1 strm'')
                        | _ => (* should be octal escape code *)
                            chkDigits StringCvt.OCT
                              (scanDigits isOctDigit getc 3 strm')
                   *)
                   | (SOME _) => NONE (* illegal escape sequence *)
                )
              (* scan (SOME("\"", strm')) should be impossible *)
              | scan (SOME(c, strm')) =
                if 32 <= Char.ord(c) andalso Char.ord(c) < 127
                then SOME(c, strm')
                else NONE
        in
            scan (getc strm)
        end

    val fromC0String = StringCvt.scanString scanC0

    fun toC0String #"\a" = "\\a"
      | toC0String #"\b" = "\\b"
      | toC0String #"\t" = "\\t"
      | toC0String #"\n" = "\\n"
      | toC0String #"\v" = "\\v"
      | toC0String #"\f" = "\\f"
      | toC0String #"\r" = "\\r"
      | toC0String #"\"" = "\\\""
      | toC0String #"\\" = "\\\\"
      | toC0String #"'" = "\\'"
      | toC0String #"\000" = "\\0"
      | toC0String #"?" = "?" (* to override Char.toCString *)
      | toC0String c = Char.toCString(c)

end (* C0Char *)
