structure SigINT :> SIGINT =
struct
  val message = "\nKeyboardInterrupt\n"
  fun interruptLoop (loop:unit -> unit) = loop ()
end

structure Server = 
   Server (structure Runline = Coin
           structure SigINT = SigINT) 
