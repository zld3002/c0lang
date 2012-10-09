(* C0 Compiler
 * Helper for compilation
 *)

CM.make "debug.cm";
SMLofNJ.exportFn ("code.heap", fn x => (Debug.debug x; OS.Process.success));
