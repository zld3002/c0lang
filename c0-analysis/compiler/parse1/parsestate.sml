(* C0 Compiler
 * Parse State System
 * Frank Pfenning <fp@cs.cmu.edu>
 *
 * This tracks filename and newline characters
 * so character positions in lexer tokens
 * can be converted to line.column format for error messages
 *)

signature PARSE_STATE =
  sig
    (* setfile(filename) sets current filename and resets newline positions *) 
    (* val setfile : string -> unit *)

    val reset : unit -> unit
    val pushfile : string -> unit
    val popfile : unit -> unit

    (* newline(pos) adds pos to current newline positions *)
    val newline : int -> unit

    (* returns the current position information based on two integer offsets *)
    val ext : int * int -> Mark.ext option
  end

structure ParseState :> PARSE_STATE =
struct

  val currFilenames = ref (nil : string list);
  val currLiness = ref (nil : int list list);

  fun reset () =
      ( currFilenames := nil ;
        currLiness := nil )
  fun pushfile (filename) =
      ( currFilenames := filename::(!currFilenames) ;
        currLiness := nil::(!currLiness) )
  fun popfile () =
      ( currFilenames := tl (!currFilenames) ;
        currLiness := tl (!currLiness) )

  fun newline pos =
      (currLiness := (pos::(hd (!currLiness)))::(tl (!currLiness)))

  (* look (pos, newline_positions, line_number) = (line, col)
   * pos is buffer position
   * newline_positions is (reverse) list of newline positions in file
   * line_number is length of newline_positions
   *)
  fun look (pos, a :: rest, n) =
      (* a is end of line n *)
      if a < pos then (n+1, pos-a)
      else look (pos, rest, n-1) 
    | look (pos, nil, n) = 
      (* first line pos is off by 1 *)
      (1, pos-1)

  fun last () = (List.length (hd (!currLiness)) + 1,  0)

  (* ext (leftpos, rightpos) = SOME((leftline, leftcol), (rightline, rightcol), filename)
   * return NONE for invalid position (0,0)
   *)
  fun ext (0, 0) = (* guessing EOF, for better error message *)
      (* NONE *)
      SOME (last (), last (), hd (!currFilenames))
    | ext (left, right) =
      SOME (look (left, hd (!currLiness), List.length (hd (!currLiness))),
	    look (right, hd (!currLiness), List.length (hd (!currLiness))),
	    hd (!currFilenames))

end
