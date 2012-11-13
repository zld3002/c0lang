

signature VERIFICATIONERROR =
sig 
   type error
   val VerificationError : (Mark.ext option * string) -> error
   val Wrap: string * error list -> error list
   val pp_error : error -> string
end

structure VError :> VERIFICATIONERROR =
struct
   datatype err = VE of Mark.ext option * string
   type error = err
   fun VerificationError x = VE x
   fun Wrap (s, l) =
     map (fn VE(e, s') => VE(e,s ^ s')) l
   fun pp_error (VE (SOME e, s)) =
                    "error at " ^ (Mark.show e) ^ ": " ^ s
     | pp_error (VE (NONE, s)) =
                    "error: " ^ s
end

signature LOCAL_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol * int
signature SYM_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol

structure LocalMap :> LOCAL_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol * int
             val compare = (fn ((v,i), (v',i')) => 
                                case Int.compare(i,i') of
                                   EQUAL => Symbol.compare (v,v')
                                 | r => r)
      end)


signature LOCAL_SET = ORD_SET where type Key.ord_key = Symbol.symbol * int
structure LocalSet :> LOCAL_SET = RedBlackSetFn (
      struct type ord_key = Symbol.symbol * int
             val compare = (fn ((v,i), (v',i')) => 
                                case Int.compare(i,i') of
                                   EQUAL => Symbol.compare (v,v')
                                 | r => r)
      end)

structure SymMap :> SYM_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)
structure SymSet = RedBlackSetFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)

