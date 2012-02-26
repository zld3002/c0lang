(* C0 Compiler
 * Helper for compilation
 *)

CM.make "csharp_sources.cm";
SMLofNJ.exportFn ("bin/cc0.heap", Top.main);
