(* ANSI Terminal color codes *)
structure Color = struct
  (* Returns empty string if C0_ENABLE_BACKTRACE=0, otherwise returns s
   * Useful for stopping colored output on output formats which don't support it
   * e.g. Autolab *)
  fun guardColor s = 
    case Option.mapPartial Int.fromString (OS.Process.getEnv "C0_ENABLE_FANCY_OUTPUT") of 
      SOME 0 => ""
    | _ => s 

  val red = guardColor "\u001b[31m"
  val purple = guardColor "\u001b[35m"
  val green = guardColor "\u001b[32m"
  val cyan = guardColor "\u001b[36m"
  val white = guardColor "\u001b[37m"

  val bold = guardColor "\u001b[1m"

  val reset = guardColor "\u001b[0m"

  fun mkBold s = bold ^ s ^ reset
end