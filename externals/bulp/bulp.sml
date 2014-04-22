signature BULP = 
sig
    type database
    type predicate
    type program = (predicate * predicate list) list
    val new : program -> database option
    val new' : Syntax.prog -> database option
    val add : database -> predicate list -> unit
    val rem : database -> predicate list -> unit
    val saturate : database -> unit
    val query : database -> predicate -> predicate list
    val query' : database -> Syntax.pred -> predicate list
    val query_bucket : database -> predicate -> ((predicate -> int) * int option) -> predicate list Array.array
    val query_array : database -> predicate -> ((predicate -> int) * int option) -> (predicate -> 'a) -> 'a list Array.array
end

signature PREDICATE =
sig
    type predicate
    val inj : predicate -> Syntax.pred
    val prj : Syntax.pred -> predicate
end

functor Bulp (Predicate:PREDICATE) : BULP = 
struct

structure Eval = McAllester

type database = Eval.database
		
type predicate = Predicate.predicate

type program = (predicate * predicate list) list

fun new pr = Eval.new (map (fn (pc, PPL) => (Predicate.inj pc, map Predicate.inj PPL)) pr)

fun new' pr = Eval.new pr

fun add db PL = Eval.add db (map Predicate.inj PL)

fun rem db PL = Eval.rem db (map Predicate.inj PL)

fun saturate db = Eval.saturate db

fun query db p = map Predicate.prj (Eval.query db (Predicate.inj p))
fun query' db p = map Predicate.prj (Eval.query db (p))

fun query_bucket db p (f,sizeopt) = 
    let 
	val result = query db p
	val size = (case sizeopt 
				of NONE => foldl (fn (a,b) => if b > f a then b else f a) 1 result
				 | SOME n => n)
	val A = Array.tabulate (size, fn i => []: predicate list)
	val _ = app (fn p' => Array.update(A, f p', p' :: (Array.sub (A, f p')))) result
    in
	A
    end

fun query_array db p (f,sizeopt) (g:predicate -> 'a) = 
    let 
	val result = query db p
	val size = (case sizeopt of NONE => foldl (fn (a,b) => if b > f a then b else f a) 1 result
				  | SOME n => n)
	val A = Array.tabulate (size, fn i => []: 'a list)
	val _ = app (fn p' => Array.update(A, f p', (g p') :: (Array.sub (A, f p')))) result
    in
	A
    end
end
