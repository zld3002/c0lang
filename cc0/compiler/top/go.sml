structure X = struct

val _ = 
OS.Process.exit (Top.main (CommandLine.name (), CommandLine.arguments ()))
handle _ => OS.Process.exit OS.Process.failure
(* Handler added because -x may result in a status message being
 * returned that MLton is not willing to use to exit.
 * - rjs Aug 31, 2013 *)
                            
end
