structure SigINT :> SIGINT =
struct
  val message = "\nKeyboardInterrupt\n"

  fun interruptLoop (loop:unit -> unit) =
     let
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
end

structure Server = 
   Server (structure Runline = Coin
           structure SigINT = SigINT) 
