(* C0 Compiler
 * Helper for compilation
 *)

CM.make "sources2.cm";
SMLofNJ.exportFn ("bin/cc0.heap", Top.main);
