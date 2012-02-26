(* Implementation of the nicities of a top-level loop; hopefully
 * modular in a decent way. Based on the Twelf implementation. 
 *
 * Requires an implementation of RUNLINE. See server-triv.sml for a 
 * trivial example implementation.
 *
 * Rob Simmons *)

signature SERVER = 
sig
    
    (* The server takes  *)
    val server : string * string list -> OS.Process.status
    val go : unit -> OS.Process.status

end (* signature SERVER *)



signature RUNLINE = 
sig

    datatype status = CONTINUE | EXIT of OS.Process.status

    (* Invoked in the start to deal with command line arguments. 
     * Should only throw the exception Error(str), which will be caught and
     * will cause the program to return with an error. *)
    val start : string * string list -> unit
 
    val runline : string -> status

end (* signature RUNLINE *)



(* Interrupt-catching environment *)

signature SIGINT =
sig

  val interruptLoop : (unit -> unit) -> unit

end (* signature SIGINT *)



functor Server 
	(structure Runline : RUNLINE
	 structure SigINT : SIGINT)
	:> SERVER = struct

  exception Done of OS.Process.status

  fun issue status = 
      case status of 
	  Runline.CONTINUE => ()
	| Runline.EXIT(status) => (print("Goodbye!\n"); raise Done(status))

  fun serveLine() = 
      case (print "(c0de) "; TextIO.inputLine (TextIO.stdIn)) of
	  NONE => Runline.EXIT(OS.Process.success)
	| SOME s => Runline.runline(s)

  fun serve() = (issue(serveLine()); serve())

  fun hstr s = (print (s ^ "\n"); issue(Runline.CONTINUE); serveTop())

  and serveTop() = 
      serve()
      handle (Error.Dynamic str) => hstr ("Error: " ^ str)
           (* | (Error.Internal str) => 
             hstr("Error: " ^ str ^ " (internal error - please report!)") *)
           | (Error.ArrayOutOfBounds (i,j)) => 
             hstr("Error: accessing element " ^ Int.toString i ^
                    " in " ^ Int.toString j ^ "-element array")
           | (Overflow) => hstr("Error: integer overflow.")
           | (Div) => hstr("Error: division by zero.")
	   | (Done status) => raise Done(status)
(*	   | exn => (print("Uncaught exception: " ^ exnMessage exn ^ "\n");
		     issue(Runline.ABORT); serveTop())  *)
 
  fun hstr s = (print (s ^ "\n"); OS.Process.failure)

  fun server(name,args) = 
      (Runline.start(name,args);
       SigINT.interruptLoop (fn () => (issue(Runline.CONTINUE); serveTop ()));
       OS.Process.failure (* Should never be reached... *))
      handle (Error.Dynamic str) => hstr ("Error: " ^ str)
           (* | (Error.Internal str) => 
             hstr("Error: " ^ str ^ " (internal error - please report!)") *)
           | (Error.ArrayOutOfBounds (i,j)) => 
             hstr("Error: accessing element " ^ Int.toString i ^
                    " in " ^ Int.toString j ^ "-element array")
           | (Overflow) => hstr("Error: integer overflow.")
           | (Div) => hstr("Error: division by zero.")
	   | (Done status) => OS.Process.success

  fun go() = server("",[])
	
end (* functor Server *)

