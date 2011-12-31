
signature CFG_SIG = sig

  type pc
  type pos = C0.pos option

  datatype 'a node 
    = Stmt of C0.simp * pos * 'a
    | Call of C0.exp option * C0.exp * C0.exp list * pos * 'a
    | PushScope of 'a
    | PopScope of 'a 
    | Test of C0.e * pos * 'a * 'a 
    | Return of C0.e option * pos

  val map : ('a -> 'b) -> 'a node -> 'b node

  type graph
  val entry_point : graph -> pc node
  val nodes : pc -> pc node

  type function = {return_type  : C0.ty, args : C0.args, graph : graph}

  type prog
  val functions : prog -> C0.fun_name -> function option 
  val ty_vars : prog -> C0.ty_name -> C0.ty option 
  val struct_defs : prog -> C0.st_name -> (C0.ty * C0.field_name) list option

end
