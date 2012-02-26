(* C0 Compiler
 * Helper for compilation
 *)

CM.make "sources1.cm";
SMLofNJ.exportFn ("bin/cc0.heap", Top.main);
