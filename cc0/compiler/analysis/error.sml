

signature VERIFICATIONERROR =
sig 
   type error
   val VerificationError : (Mark.ext option * string) -> error
   val VerificationNote : (Mark.ext option * string) -> error
   val wrap: string * error list -> error list
   val enclose: error -> Mark.ext option -> error
   val pp_error : error -> string
end

structure VError :> VERIFICATIONERROR =
struct
   datatype err = VE of Mark.ext option * string
                | VN of Mark.ext option * string
   type error = err
   fun VerificationError x = VE x
   fun VerificationNote x = VN x
   fun wrap (s, l) =
     map (fn VE(e, s') => VE(e,s ^ s') | VN(e, s') => VN(e, s ^ s')) l
   fun enclose e r =
     case r of 
        NONE => e
      | SOME r =>
         case e of
            VE (NONE, s) => VE(SOME r, s)
          | VN (NONE, s) => VN(SOME r, s)
          | _ => e
   fun make_msg kind ext msg =
      (Option.getOpt(Option.map (Mark.show) ext,"")) ^
      (String.concat[":", kind, ":", msg, "\n"]) ^
      (Option.getOpt(Option.map (Mark.show_source) ext,""))
         
   fun pp_error (VE (ext, msg)) = make_msg "error" ext msg
     | pp_error (VN (ext, msg)) = make_msg "note" ext msg 
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

