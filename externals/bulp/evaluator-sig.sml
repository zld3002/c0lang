signature EVALUATOR = 
sig
    type database

    val new : Syntax.prog -> database option

    val add : database -> Syntax.pred list -> unit

    val rem : database -> Syntax.pred list -> unit

    val saturate : database -> unit

    val query : database -> Syntax.pred -> Syntax.pred list
end
