(* ANSI Terminal color codes *)
structure Color = struct 
  val red = "\u001b[31m"
  val purple = "\u001b[35m" (* Technically magenta... *)
  val green = "\u001b[32m"
  val cyan = "\u001b[36m"
  val white = "\u001b[37m"

  val bold = "\u001b[1m"

  val reset = "\u001b[0m"

  fun mkBold s = bold ^ s ^ reset 
end