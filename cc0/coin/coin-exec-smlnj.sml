CM.make "coin-core.cm";
SMLofNJ.exportFn ("coin-exec.heap", fn x => CoinExec.go x);
