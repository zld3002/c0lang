(* Exec implements the stateful operational semantics of commands in the 
 * C0 intermediate language. *)

signature EXEC =
sig

(* INTERNAL STATE *)

(* The ConcreteState.state object can have any number of
 * instantiations, but in an interpreter we only want there to be a
 * single instantiation that all our computation is relative
 * to. This is that state. *)
val state: (Symbol.symbol * Mark.ext) ConcreteState.state

(* Reset the module's internal state. *)
val reset: unit -> unit

(* print local variables *)
val print_locals : unit -> unit



(* STEP TO NEXT COMMAND
 * 
 * The result of executing any "step over" operation is either to
 * halt - possibly with a value (ReturnSome v), possibly without
 * (ReturnNone) - or else to change the state imperatively and
 * return the next program counter location in the current hunk of
 * bytecode. *)

datatype step_info = 
   ReturnNone 
 | ReturnSome of ConcreteState.value 
 | PC of int

val step: C0Internal.program * int -> step_info



(* STEP INTO FUNCTION
 * 
 * When we try to "step into" a function value, it may just go ahead and
 * merrily run the native function, or we may get the return type and the
 * hunk of code associated with an interpreted call. *)

datatype call_info = 
   Native of ConcreteState.value 
 | Interp of CodeTab.fun_ty * C0Internal.program 

val call_step: 
   Symbol.symbol * ConcreteState.value list * Mark.ext -> call_info



(* BIG-STEP EVALUATION *)

(* Call a function *)
val call: 
   Symbol.symbol * ConcreteState.value list * Mark.ext -> ConcreteState.value

(* Run a compiled command *)
val exec: C0Internal.program -> ConcreteState.value

end
