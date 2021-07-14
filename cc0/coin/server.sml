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

    (* Gets the prompt + current completion list *)
    val prompt : unit -> (string * string list) 
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
  let 
    val (prompt, completions) = Runline.prompt ()
    val input = C0ReadLine.readline prompt completions
  in 
    case input of
      NONE => Runline.EXIT(OS.Process.success)
    | SOME s => Runline.runline(s)
  end 

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
                if i < 0
                then hstr ("Error: accessing negative element in "
                           ^Int.toString j^"-element array")
                else hstr ("Error: accessing element "^Int.toString i
                           ^" in "^Int.toString j^"-element array")
           | (Overflow) => hstr("Error: integer overflow.")
           | (Error.ArraySizeNegative i) => 
                hstr("Error: cannot allocate a negative-sized array.")
           | (Div) => hstr("Error: division by zero.")
           | (Error.Allocation) => hstr("Error: allocation failed!")
           | (Error.Compilation) => hstr("Error: could not compile.")
           | (Error.AssertionFailed s) => hstr s
           | (Error.ErrorCalled s) => hstr ("Error: "^s)
           | (Done status) => raise Done(status)
           | (Error.Dynamic str) => 
                hstr ("Error (DYNAMIC SEMANTICS, PLEASE REPORT): " ^ str)
           | (Error.Internal str) => 
                hstr("Error (INTERNAL, PLEASE REPORT): " ^ str)
           | exn => hstr("Uncaught exception: " ^ exnMessage exn ^ "\n") 
 
  fun hstr s = (print (s ^ "\n"); OS.Process.failure)

  fun server(name,args) = 
  let 
    val () = C0ReadLine.init ()

    val result = 
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

    val () = C0ReadLine.finish ()
  in 
    result 
  end 

  fun go() = server(CommandLine.name (), CommandLine.arguments ())
	
end (* functor Server *)

