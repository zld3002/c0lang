signature OP_SEM = sig

  type value 
  type state
  type position = (CFG.pc -> CFG.pc CFG.node) * CFG.pc CFG.node
       
  exception Done of state * value
  val step : CFG.prog -> state -> position -> position

  val run : CFG.prog * int -> Word32.word option

end
