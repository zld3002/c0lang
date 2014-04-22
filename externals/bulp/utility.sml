signature UTILITY = 
sig
    (*Print string to screen *)
    val say : string -> unit (*Adds newline at the end*)
    val say' : string -> unit (*No newline*)

    val min : int list -> int
    val max : int list -> int

    (*Set operations (very naive implementations)*)
    val member : 'a -> 'a list -> bool
    val unique : 'a list -> 'a list (*removes duplicate elements*)
    val intersection : 'a list -> 'a list -> 'a list
    val difference : 'a list -> 'a list -> 'a list (*remove second list from first*)
    val eq : 'a list -> 'a list -> bool
    val eq_classes : ('a * 'a -> bool) -> 'a list -> 'a list list
end

structure Utility = 
struct
    fun say' s = TextIO.output(TextIO.stdOut, s)
    fun say s = say' (s ^ "\n")

    fun min I = foldl Int.min (case Int.maxInt of NONE => 65535 | SOME i => i) I

    fun min I = foldl Int.max (case Int.minInt of NONE => ~65536 | SOME i => i) I

    fun member x [] = false
      | member x (e::L) = if x = e then true else member x L

    fun unique [] = []
      | unique (e::L) = if member e L then unique L else e::(unique L)

    fun intersection [] L2 = []
      | intersection (e::L1) L2 = if member e L2 then e::(intersection L1 L2) else intersection L1 L2

    fun difference [] L2 = []
      | difference (e::L1) L2 = if member e L2 then difference L1 L2 else e::(difference L1 L2)

    fun eq' [] [] _ _ = true
      | eq' (l1::L1) (l2::L2) L1' L2' = if member l1 L2' andalso member l2 L1' then eq' L1 L1 L1' L2' else false
      | eq' _ _ _ _ = false

    fun eq L1 L2 = eq' L1 L2 L1 L2



    fun member' f x [] = false
      | member' f x (e::L) = if f(e,x) then true else member' f x L

    fun difference' f [] L2 = []
      | difference' f (e::L1) L2 = if member' f e L2 then difference' f L1 L2 else e::(difference' f L1 L2)		   

    fun eq_classes f [] = []
      | eq_classes f (e::L) = 
	let 
	    val E = e :: (List.filter (fn x => f (e,x)) L)
	in
	    E :: (eq_classes f (difference' f L E))
	end
end
