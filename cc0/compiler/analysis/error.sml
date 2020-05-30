

signature VERIFICATIONERROR =
sig 
   type error
   val VerificationError : (Mark.ext option * string) -> error
   val VerificationNote : (Mark.ext option * string) -> error
   
   val pp_error : error -> unit
   
   (*  collect: execute a function, collecting the errors that are thrown
                into a list, and returning the produced value.*)
   val collect: (unit -> 'a) -> (error list * 'a)
   val throw: error -> unit
   val wrap: string * error list -> error list
   val enclose: error -> Mark.ext option -> error
   
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
          
   val tabToSpace = String.translate (fn #"\t" => " " | c => String.str c)
         
   fun pp_error (VE (ext, msg)) = ErrorMsg.error ext msg 
     | pp_error (VN (ext, msg)) = ErrorMsg.info ext msg  
     
   local 
      val l = ref ([] : error list)
   in
       fun collect f = 
          let val prevl = !l
              val _ = l := []
              val v = f()
              val es = rev(!l) (* reverse to put things back in order of throwing.*)
              val _ = l := prevl  
          in (es, v) end
       fun throw e = (l := e :: !l)
   end
end

