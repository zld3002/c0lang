structure SigINT :> SIGINT =
struct

  val message = "Interrupt (type \"q\" or \"quit\" to exit)\n"

  fun interruptLoop (loop:unit -> unit) =
     let
	(* open MLton *)
	val _ =
	   MLton.Cont.callcc
	   (fn k =>
	    MLton.Signal.setHandler
	    (Posix.Signal.int,
	     MLton.Signal.Handler.handler
		 (fn _ =>
		     MLton.Thread.prepare
		     (MLton.Thread.new (fn () => 
                                           let in 
                                             print message;
                                             MLton.Cont.throw (k, ())
                                           end),
		      ()))))
     in
	loop ()
     end

end;
