(* C0 Compiler
 * Simple non-memoizing streams
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature STREAM =
sig
    (* simple (non-memoizing) streams *)
    datatype 'a front
      = Cons of 'a * (unit -> 'a front)
      | Nil

    type 'a stream = unit -> 'a front
    val force : 'a stream -> 'a front
    val fromList : 'a list -> 'a stream
    val isNil : 'a front -> bool
end

structure Stream :> STREAM =
struct
   datatype 'a front =
      Cons of 'a * (unit -> 'a front)
    | Nil

   type 'a stream = unit -> 'a front
   fun force ts = ts ()
   fun fromList [] () = Nil
     | fromList (t :: ts) () = Cons (t, fromList ts)
   fun isNil Nil = true
     | isNil _ = false
end
