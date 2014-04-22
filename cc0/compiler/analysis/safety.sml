
(* represents an abstract state of the program at a specific point. *)
signature CONTEXT = 
sig
   type context
   (* the bottom context, empty context (top), a bottom predicate, greatest
      lower bound (conjunction), least upper bound (disjunction), and a pretty
      printer. *)
   val bot   : context
   val empty : context
   val isBot : context -> bool   
   val glb   : context * context -> context
   val lub   : context * context -> context
   val pp_context : context -> string
   
   (* Havoc a heap, but only in the given locations *)
   val havoc : Modifies.modifies -> context -> context
   (* analyze an assignment *)
   val analyzeAssign : context -> Gcl.lhs * Gcl.rhs -> context
   (* learn facts from a boolean expression, checking safety as well. *)
   val analyzeBoolExpr : context -> Gcl.expr -> (context * context)
   val inDomain : context -> Gcl.expr -> bool
   
   (*val proveBoolExpr : context -> (Gcl.expr) -> context *)
   
   val bindSummary : Symbol.symbol -> Gcl.ident list -> context -> unit
end

signature SAFETYANALYSIS = 
sig
   structure Context: CONTEXT
   (* check safety for the function. Produces a list of safety violations. *)
   val checkFunc : Gcl.ident -> Gcl.func -> (VError.error list)
end

(* generates a SAFETYANALYSIS which uses the given CONTEXT to check the safety
   of a program. *)
functor SafetyAnalysis(Ctx : CONTEXT) :> SAFETYANALYSIS =  
struct
   open VError
   open Gcl
   structure Context = Ctx
   
   type env = (Mark.ext option * Gcl.ident * int option)
   fun emptyEnv f = (NONE, f, NONE)
   fun extOfEnv (ext,_,_) = ext
   fun msgOfEnv (_,_,SOME l) = Trans.lookupMsg l
     | msgOfEnv (_,_,NONE) = NONE
   fun inLabel (ext,f, _) label =
     (case Trans.lookupExt label of SOME e => SOME e
       | _ => ext, f, SOME label)
   
   fun checkAnno gamma env (Anno (wf, ck, assum)) =
      let val (_, []) = checkStmt gamma env wf
          val (_, []) = checkStmt gamma env ck
      in () end
    
   and assumeAnno gamma env (Anno (wf, ck, assum)) = 
      let val (gamma'', []) = checkStmt gamma env assum
      in gamma'' end
      
      
   and checkStmt gamma env s = 
      if Ctx.isBot gamma then (gamma, []) else 
      case s of
         If(e, a, b) => 
            let val (et, ef) = Ctx.analyzeBoolExpr gamma e
                val (ctxa, breaka) = checkStmt et env a
                val (ctxb, breakb) = checkStmt ef env b
            in (Ctx.lub (ctxa,ctxb), breaka @ breakb) end
       | While (gs, g, i, b) =>
          (let val _ = checkAnno gamma env i
               val genericCtx = Ctx.havoc (Modifies.lookup_while (#2 env,
                                           case #3 env of SOME x => x
                                             | NONE => raise Fail
                                                          "expected label on while statment"))
                                           gamma
               val postInv = assumeAnno genericCtx env i
               val (preGuard, []) = checkStmt postInv env gs
               val (gt,gf) = Ctx.analyzeBoolExpr preGuard g
               val (postBody, breaks) = checkStmt gt env b
               val _ = checkAnno postBody env i
           in (gf, breaks) end)
       | Assume e => (#1(Ctx.analyzeBoolExpr gamma e), [])
       | Check a => (checkAnno gamma env a; (assumeAnno gamma env a,[]))
       | Assert e => 
          (if not (Ctx.isBot (#2(Ctx.analyzeBoolExpr gamma e))) andalso 
                  (Ctx.inDomain gamma e) then
             VError.throw(VerificationError(extOfEnv env, getOpt(msgOfEnv env, "could not prove assertion")))
            else ();
            (gamma, []))
       | Assign (l,r) => (Ctx.analyzeAssign gamma (l,r), [])
       | Block (i,s) =>
           let val (endctx, breaks) = checkStmt gamma env s
               val (matched, rest) = List.partition (fn (j,_) => i = j) breaks
               val ctx = foldl Ctx.lub endctx (map #2 matched)
           in (ctx, rest) end
       | Break i => (Ctx.bot, [(i, gamma)])
       | Seq [] => (gamma, [])
       | Seq (s::ss) => 
            let val (g', breaks) = checkStmt gamma env s
                val (g'', breaks') = checkStmt g' env (Seq ss)
            in (g'', breaks @ breaks') end
       | Comment _ => (gamma, [])
       | LabeledS (label, s) =>
            checkStmt gamma (inLabel env label) s
       
   (* string all of the above together and collect all found errors. *)
   fun checkFunc name (Gcl.Function(rtp, types, formals, reqs, body, ens)) =
      #1( VError.collect (fn () => 
          let val preBody = assumeAnno Ctx.empty (emptyEnv name) reqs
            (*val _ = AUtil.say ("PreBody Context: " ^ Ctx.pp_context preBody) *)
              val (postBody, []) = checkStmt preBody (emptyEnv name) body
              val _ = checkAnno postBody (emptyEnv name) ens
              val summary = assumeAnno postBody (emptyEnv name) ens
              val _ = Ctx.bindSummary name (map #1 formals) summary
          in () end)
        )
   
end
