(* C0ffi Wrapper Generater *)

CM.make "makelibs/wrappergen.cm";
SMLofNJ.exportFn ("bin/wrappergen.heap", LoadH0.wrappergen);
