
structure SymOrd = struct
  type ord_key = Symbol.symbol
  val compare = Symbol.compare
end
structure IntOrd = struct
  type ord_key = int
  val compare = Int.compare
end

functor PairOrd(structure A: ORD_KEY structure B: ORD_KEY)
   : ORD_KEY where type ord_key = (A.ord_key * B.ord_key) =
struct
  type ord_key = (A.ord_key * B.ord_key)
  fun compare ((a1,b1),(a2,b2)) = 
    case A.compare(a1,a2) of
       LESS => LESS
     | EQUAL => B.compare(b1,b2)
     | GREATER => GREATER
end


signature LOCAL_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol * int
signature SYM_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol
structure LocalOrd = 
      struct type ord_key = Symbol.symbol * int
             val compare = (fn ((v,i), (v',i')) => 
                                case Int.compare(i,i') of
                                   EQUAL => Symbol.compare (v,v')
                                 | r => r)
      end
structure LocalMap :> LOCAL_MAP = RedBlackMapFn (LocalOrd)


signature LOCAL_SET = ORD_SET where type Key.ord_key = Symbol.symbol * int
structure LocalSet :> LOCAL_SET = RedBlackSetFn (LocalOrd)

structure SymMap :> SYM_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)
structure SymSet = RedBlackSetFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)

structure AUtil = struct
  
  val debug = ref true
  fun say s = 
     if !debug then 
        TextIO.output(TextIO.stdErr, s ^ "\n")
     else ()

  fun collect ord l =
     let val sorted = ListMergeSort.sort (fn ((a,_), (b,_)) => ord(a,b) = GREATER) l
         fun group [] = []
           | group ((a,b)::r) =
               case group r of 
                  [] => [(a,[b])]
                | (a',grp) :: tl => case ord(a,a') of
                                             EQUAL => (a',b::grp) :: tl
                                           | _ => (a,[b]) :: (a',grp) :: tl
     in group sorted end
   
end
