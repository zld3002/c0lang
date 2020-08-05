(* 
 * CC0 code warnings
 * Ishan Bhargava (ibhargav@andrew)
 * November 2019 
 * 
 * Currently this will warn about 
 * unused local variables within
 * a function, unused expression results,
 * and unreachable code.
 * 
 * Each warning will use Flags.warning_enabled
 * to determine if it should report something or not 
 *)

signature CODEWARN = sig
  (* Prints out all warnings using the warning function *)
  val warn_program: Ast.program -> unit
end

structure CodeWarn :> CODEWARN = struct
  fun warn_program gdecls = (
    WarnUnused.warn_program gdecls;
    WarnUnreachable.warn_program gdecls
  )
end