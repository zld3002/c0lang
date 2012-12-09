
(* represents an abstract state of the program at a specific point. *)
signature CONTEXT = 
sig
   type context
   (* the bottom context, empty context (top), a bottom predicate, greatest
      lower bound (conjunction), least upper bound (disjunction), and a pretty
      printer. *)
   val bot : context
   val empty : context
   val isBot : context -> bool
   val glb : context * context -> context
   val lub : context * context -> context
   val pp_context : context -> string
   
   (* given a local SSA definition, infer facts while checking safety. *)
   val analyzeDef : (Ast.tp SymMap.map) -> context -> 
         (Mark.ext option * AAst.loc * AAst.aexpr) -> (VError.error list * context)
   (* given a phi definition, learn about the new definition. *)
   val analyzePhi : (Ast.tp SymMap.map) -> context -> AAst.aphi -> context
   (* given a phi definition, learn about the new definition assuming that the
      given branch index is the path that is taken. *)
   val analyzePhi' : (Ast.tp SymMap.map) -> context -> AAst.aphi -> int -> context
   (* lose all information about the definition in the phi. *)
   val havocPhi : (Ast.tp SymMap.map) -> context -> AAst.aphi -> context
   (* learn facts from an expression, checking safety as well. *)
   val analyzeExpr : (Ast.tp SymMap.map) -> context ->
         (Mark.ext option * AAst.aexpr) -> (VError.error list * context)
   (* learn facts from an return, checking safety as well. *)
   val analyzeReturn : Ast.tp -> (Ast.tp SymMap.map) -> context ->
         (Mark.ext option * AAst.aexpr) -> (VError.error list * context)
   (* analyze a boolean expression, given the context that results when it evalutes
      to true and the one when it evaluates to false. *)
   val analyzeBoolExpr : (Ast.tp SymMap.map) -> context ->
         (Mark.ext option * AAst.aexpr) -> (VError.error list * context * context)
   (* attempt to prove a boolean expression has the given truth value. *)
   val proveBoolExpr : (Ast.tp SymMap.map) -> context ->
         (Mark.ext option * AAst.aexpr) -> bool -> (VError.error list * context)
end

signature SAFETYANALYSIS = 
sig
   structure Context: CONTEXT
   (* given a symbol table, preconditions, the function body, and postconditions,
      check safety for the function. Produces a list of errors, for things like
      safety violations. Note ensures aren't checked very well. *)
   val checkFunc : Ast.tp -> Ast.tp SymMap.map -> AAst.aexpr list -> AAst.astmt -> AAst.aexpr list -> (VError.error list)
end

(* generates a SAFETYANALYSIS which uses the given CONTEXT to check the safety
   of a program. *)
functor SafetyAnalysis(Ctx : CONTEXT) :> SAFETYANALYSIS =  
struct
   structure Context = Ctx
   
   open VError
   
   (* get the extent of an expression if available, otherwise use ext.
      used for getting the extent of an annotation. *)
   fun getExt ext e =
     case e of AAst.MarkedE m => Mark.ext m
     | _ => ext
     
   (* the code to check a while statement is long and complicated, so it is split
      into a helper function. It takes roughly the same arguments as checkStmt. *)
   fun checkWhile rtp types gamma ext (phis, guard, invs, body, endphis) =
     let (* analyze the phi definitions, assuming the incoming control path is
            index j. *)
         fun analyzePhis g j = 
            foldl (fn (phi, ctx) => Ctx.analyzePhi' types ctx phi j) g phis
         (* check that the invariants hold under a given context. *)
         fun checkInvs g =
            foldl (fn (inv, (errs, ctx)) =>
                        let val (e, g) = Ctx.proveBoolExpr types ctx (ext,inv) true
                        in (errs@e, g) end)
                  ([], g) invs
         (* learn from the invariants, without trying to prove them. *)
         fun analyzeInvs g =
            foldl (fn (inv, (errs, ctx)) =>
                        let val (e, tg, fg) = Ctx.analyzeBoolExpr types ctx (ext,inv)
                        in (errs@e, tg) end)
                  ([], g) invs
         (* check the invariants on entering the loop: *)
         val (errFirst, _) = checkInvs (analyzePhis gamma 0)
         val errFirst = Wrap ("loop inv may not hold on entry: ", errFirst)
         (* generate a generic context that is from any number of iterations arround
            the loop: *)
         val loopCtx = foldl (fn (phi, g) => Ctx.havocPhi types g phi) gamma phis
         (* learn from that context, as the context at the start of a generic
            loop iteration. *)
         val (einvs, tinvs) = analyzeInvs loopCtx 
         (* get information from the guard. We only continue in the loop if the
            guard is true, and exit otherwise, so we need that information when
            checking the body. *)
         val (eguard, tg, fg) = Ctx.analyzeBoolExpr types tinvs (ext, guard)
         (* now check the body. At the end of the body's execution, we have
            ctxBEnd, as well as contexts rets, brks, conts representing the return
            value contexts, the break statement contexts, and the continue statement
            contexts.*)
         val (errBody, ctxBEnd, rets, brks, conts) = checkStmt rtp types tg (ext, body)
         (* check that the loop invaraints hold if the loop completes normally.
            note that if the loop never reaches the end (always breaks or something),
            then this context will be Bot and the invariants will trivially be
            provable. *)
         val (errSec, _) = checkInvs (analyzePhis ctxBEnd 1)
         (* check all the ways that the continue statements can loop arround.
            note because the way the SSA picks up continues into the phi definition
            and the way checkStmt collects the contexts are the same, the indices
            are the same (except offset by 2 because of the entering of the loop
            and normal loop return to top. *)
         val errSec = Wrap ("loop inv may not hold when body completes: ", errSec)
         fun checkConts i cs = 
             case cs of [] => []
                      | c::cs' => (#1(checkInvs (analyzePhis c i))) @
                                  (checkConts (i+1) cs')
         val errConts = checkConts 2 conts
         val errConts = Wrap ("loop inv may not hold on continue: ", errConts)
         val ctxend = Ctx.lub (fg, foldl Ctx.lub Ctx.bot brks)
         val ctxend' = foldl (fn (phi, g) => Ctx.analyzePhi types g phi) ctxend phis
         
     in (* now collect all the errors, and or together all the break statements,
           along with the negation of the loop guard. *)
        (errFirst @ einvs @ eguard @ errBody @ errSec @ errConts,
         ctxend', rets, [], []) end
   
   (* (errs, gamma', rets, brks, conts) = checkStmt types gamma (ext, s) *)
   and checkStmt rtp types gamma (ext, s) = 
      if Ctx.isBot gamma then ([], gamma, [], [], [])
      else 
      case s of
         AAst.Nop => ([], gamma, [], [], [])
       | AAst.Seq(a,b) => 
           let val (err, g', r1, b1, c1) = checkStmt rtp types gamma (ext, a)
               val (err', g'', r2, b2, c2) = checkStmt rtp types g' (ext, b)
           in (err @ err', g'', r1@r2, b1@b2, c1@c2) end
       | AAst.Assert e => let val(err, t,f) = (Ctx.analyzeBoolExpr types gamma (ext,e))
                          in (err, t, [], [], []) end
       | AAst.Error e => raise Fail "Rob doesn't know what to do here"
            (* This obviously isn't right. -rjs Dec 8 2012 *) 
       | AAst.Annotation e => 
           let val (err, t) = Ctx.proveBoolExpr types gamma (ext,e) true
               val err' = if Ctx.isBot t then [VerificationError (getExt ext e,
                           "assert cannot be true: " ^ (AAst.Print.pp_astmt s))]
                         else []
           in (err @ err', t, [], [], []) end
       | AAst.Def (l, e) => 
           let val (errs, gamma') = Ctx.analyzeDef types gamma (ext, l, e)
           in (errs, gamma', [], [], []) end
       | AAst.Assign (lv, _, e) => 
           let val (err, gamma') = Ctx.analyzeExpr types gamma (ext, lv)
               val (err', gamma'') = Ctx.analyzeExpr types gamma' (ext, e)
           in (err @ err', gamma'', [], [], []) end
       | AAst.Expr e => 
           let val (errs, gamma') = Ctx.analyzeExpr types gamma (ext, e)
           in (errs, gamma', [], [], []) end
       | AAst.Break => ([], Ctx.bot, [], [gamma], [])
       | AAst.Continue => ([], Ctx.bot, [], [], [gamma])
       | AAst.Return (SOME e) =>
           let val (errs, gamma') = Ctx.analyzeReturn rtp types gamma (ext, e)
           in (errs, gamma', [], [], []) end
       | AAst.Return (NONE) => ([], Ctx.bot, [gamma], [], [])
       | AAst.If (cond, t, f,phis) => 
           let val (err, ct, cf) = Ctx.analyzeBoolExpr types gamma (ext, cond)
               val err' = (if Ctx.isBot ct then
                           [VerificationError (ext, "then branch never taken")]
                           else []) @ 
                          (if Ctx.isBot cf then
                           [VerificationError (ext, "then branch always taken")]
                           else [])
               val (errt, gt, r1, b1, c1) = (checkStmt rtp types ct (ext, t))
               val (errf, gf, r2, b2, c2) = (checkStmt rtp types cf (ext, f))
           in (err @ err' @ errt @ errf, foldl (fn (phi, g) => Ctx.analyzePhi types g phi) (Ctx.glb (gt, gf)) phis,
               r1@r2, b1@b2, c1@c2) end
       | AAst.While (phis, guard, invs, body,endphis) => 
           checkWhile rtp types gamma ext (phis, guard, invs, body, endphis)
       | AAst.MarkedS ms => checkStmt rtp types gamma (Mark.ext ms, Mark.data ms)
       (*| _ => raise AAst.UnsupportedConstruct ("checkStmt: " ^ (AAst.Print.pp_astmt s))*)
       
   (* learn from the function preconditions, not attempting to prove them but
      checking safety. *)
   fun checkRequires types reqs = 
     let fun check (spec, (errs, gamma)) =
            let val (e, t, f) = Ctx.analyzeBoolExpr types gamma (NONE, spec)
            in (errs @ e, t) end
     in
       foldl (check) ([], Ctx.empty) reqs
     end
   (* check that the ensures clause are safe and attempt to prove them. note this
      currently doesn't work very well because the return value is not tracked in
      the context. *)
   fun checkEnsures types ctx ens = 
     let fun check (spec, (errs, g)) =
            let val (e, g') = Ctx.proveBoolExpr types g (NONE, spec) true
            in (errs @ e, g') end
     in
       foldl (check) ([], ctx) ens
     end
   (* string all of the above together and collect all found errors. *)
   fun checkFunc rtp types reqs body ens =
      let val (errs, ctx) = checkRequires types reqs
          val (errs', ctx', rets, _, _) = checkStmt rtp types ctx (NONE, body)
          val (errs'', ctx'') = checkEnsures types (foldl Ctx.lub ctx' rets) ens
      in errs @ errs' @ errs'' end
   
end
