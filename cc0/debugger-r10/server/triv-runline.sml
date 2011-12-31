(* Trivial implementations of the Runline signature (echo) *)

structure Runline_Triv :> RUNLINE = struct

 exception Error of string 
		    
 datatype status = 
	  OK                         (* Normal execution                  *)
	| ABORT                      (* Program error                     *)
	| NOTHING                    (* Not ready for a response          *)
	| EXIT of OS.Process.status  (* Terminate the program w/ status   *)

 fun args(_,_) = OK

 fun runline "quit\n" = EXIT(OS.Process.success)
   | runline "error\n" = raise Error("The string \"error\" was entered")
   | runline "fail\n" = raise Fail("The string \"fail\" was entered")
   | runline "terrible\n" = raise Domain
   | runline s = (print(s); OK)

 fun start _ = print "Runline trivial (echo)\n"

end

(* Trivial implementation of SIGINT *)

structure SigINT_Triv :> SIGINT = struct

 fun interruptLoop loop = loop();

end

(* Trivial implementation of Server *)

structure Server_Triv =
  Server (structure Runline = Runline_Triv
          structure SigINT = SigINT_Triv) 

val _ = OS.Process.exit
        (Server_Triv.server (CommandLine.name (),
			    CommandLine.arguments ()))
