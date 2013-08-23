signature STD =
sig

    (* check adherence to std and raise ErrorMsg.Error if violated *)
    val check : Ast.program -> unit

end
