(* C0 Compiler
 * Constraint store for VCGen
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature CONDITIONS =
sig

  val assert : AAst.aexpr -> unit

  (* Should really return a datatype containing more information, but just use
   * a boolean for now. *)
  val check : unit -> bool

  (* Stores the current set of assertions for later use *)
  val push : unit -> unit

  (* Updates the assertions to be the most recently stored  *)
  val pop : unit -> unit

end

structure Conditions :> CONDITIONS =
struct

  fun assert e = ()

  fun check () = true

  fun push () = ()
  fun pop () = ()

end
