(* C0 Compiler
 * Error messages
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature ERRORMSG =
sig
  (* clears out all errors from the system *)
  val reset : unit -> unit
        
  (* global flag that indicates whether there were errors *)
  val anyErrors : bool ref

  (* sets the error flag and prints out an error message, does NOT raise ERROR *)
  val error : Mark.ext option -> string -> unit
  (* same, but does not increment error count *)
  val warn : Mark.ext option -> string -> unit

  (* generic code stopping exception *)
  exception Error
end

structure ErrorMsg :> ERRORMSG =
struct
  (* Initial values of compiler state variables *)
  val anyErrors = ref false
                   
  fun reset () = ( anyErrors := false )
  
  (* We turn tabs into spaces because they are counted as a single character in
     the extents, so in order for the emphasis to be correct we need each
     character to be one column wide. *)     
  val tabToSpace = String.translate (fn #"\t" => " " | c => String.str c)
  fun msg str ext note =
      ( ignore (Option.map (TextIO.print o Mark.show) ext)
      ; List.app TextIO.print [":", str, ":", note, "\n"]
      ; ignore (Option.map (TextIO.print o tabToSpace o Mark.show_source) ext)
      )
    
  fun error ext note = (anyErrors := true; msg "error" ext note)
  fun warn ext note = msg "warning" ext note
               
  (* Print the given error message and then abort compilation *)
  exception Error
end
