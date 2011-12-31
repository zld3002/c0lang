signature POS = 
sig
    type position

    val bogus : position
	 
    val mk_pos : int * int * int * int -> position

    val merge : position -> position -> position

    val print : position -> string
end

structure Pos :> POS =
struct
type position
  = {l1 : int, c1 : int, l2 : int, c2 : int}

val bogus
  = {l1 = 0, c1 = 0, l2 = 0, c2 = 0}

fun mk_pos (l1, c1, l2, c2) 
  = {l1=l1, c1=c1, l2=l2, c2=c2}

fun merge (p1:position) (p2:position) 
  = {l1 = #l1 p1, c1 = #c1 p1, l2 = #l2 p2, c2 = #c2 p2}

fun print (p:position) 
  = "(" ^ Int.toString (#l1 p) ^ "," ^ Int.toString  (#c1 p) ^ ") " ^
    "(" ^ Int.toString (#l2 p) ^ "," ^ Int.toString  (#c2 p) ^ ")"

end
