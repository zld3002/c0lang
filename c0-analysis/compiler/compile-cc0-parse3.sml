(* C0 Compiler
 * Helper for compilation
 *)

CM.make "sources3.cm";
SMLofNJ.exportFn ("bin/cc0.heap", Top.main);
