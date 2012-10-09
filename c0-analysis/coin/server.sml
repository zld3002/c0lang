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

    (* Invoked in the start to deal with command line arguments. *)
    (* Returning a status causes the server to quit without entering the loop *)
    val start : string * string list -> OS.Process.status option
    val restart : unit -> unit

    val prompt : unit -> unit
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
      case (Runline.prompt(); TextIO.inputLine (TextIO.stdIn)) of
	  NONE => Runline.EXIT(OS.Process.success)
	| SOME s => Runline.runline(s)

  fun serve() = (issue(serveLine()); serve())

  fun hstr s = (print (s ^ "\n"); 
                Runline.restart(); 
                issue(Runline.CONTINUE); 
                serveTop())

  and serveTop() = 
      (serve())
      handle (Error.Uninitialized) => hstr ("Error: uninitialized value used")
           | (Error.NullPointer) => hstr ("Error: null pointer was accessed")
           | (Error.ArrayOutOfBounds (i,j)) => 
             hstr("Error: accessing element " ^ Int.toString i ^
                    " in " ^ Int.toString j ^ "-element array")
           | (Overflow) => hstr("Error: integer overflow.")
           | (Error.ArraySizeNegative i) => 
             hstr("Error: invalid array size " ^ Int.toString i ^ " .")
           | (Div) => hstr("Error: division by zero.")
           | (Error.Allocation) => hstr("Error: allocation failed!")
           | (Error.Compilation) => hstr("Error: could not compile.")
           | (Error.AssertionFailed s) =>  
             hstr s
           | (Done status) => raise Done(status)
           | (Error.Dynamic str) => 
             hstr ("Error (DYNAMIC SEMANTICS, PLEASE REPORT): " ^ str)
           | (Error.Internal str) => 
             hstr("Error (INTERNAL, PLEASE REPORT): " ^ str)
           | exn => hstr("Uncaught exception: " ^ exnMessage exn ^ "\n")
 
  fun hstr s = (print (s ^ "\n"); OS.Process.failure)

  fun server(name,args) = 
      (case Runline.start(name,args) of
         NONE => 
         (SigINT.interruptLoop (fn () => (Runline.restart(); serveTop ()));
          OS.Process.failure (* Should never be reached... *))
       | SOME status => status) 
       handle (Error.Uninitialized) => hstr ("Error: uninitialized value used")
           | (Overflow) => hstr("Error: integer overflow.")
           | (Div) => hstr("Error: division by zero.")
           | (Error.Compilation) => hstr("Error: could not compile.")
           | (Error.Dynamic str) => 
             hstr ("Error (DYNAMIC SEMANTICS, PLEASE REPORT): " ^ str)
           | (Error.Internal s) => 
             hstr("Error (INTERNAL, PLEASE REPORT): \"" ^ s ^ "\"")
           | (Done status) => OS.Process.success 

  fun go() = server(CommandLine.name (), CommandLine.arguments ())
	
end (* functor Server *)

