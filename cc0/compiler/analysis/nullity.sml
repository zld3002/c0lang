(* A CONTEXT which tracks only nullity information. *)
structure NullityContext :> CONTEXT =
struct
   datatype chain = Var of Gcl.ident
                  | Field of chain * Gcl.field
                  | NullChain
   
   fun pp_chain (Var l) = Symbol.name l
     | pp_chain (Field(c, f)) = (pp_chain c) ^ "->" ^ (Gcl.pp_field f)
     | pp_chain (NullChain) = "NULL"
   structure ChainOrd = struct
     type ord_key = chain
     fun compare (NullChain, NullChain) = EQUAL
       | compare (NullChain, _) = LESS
       | compare (_, NullChain) = GREATER
       | compare (Var _ , Field _) = GREATER
       | compare (Var s, Var t) = Symbol.compare (s,t)
       | compare (Field _, Var _) = LESS
       | compare (Field (c1, f1), Field(c2, f2)) =
           case compare(c1, c2) of 
              EQUAL => Gcl.compareField (f1, f2)
            | ord => ord
   end
   structure PairChainOrd = PairOrd(structure A = ChainOrd structure B = ChainOrd)
   structure CMap = RedBlackMapFn(ChainOrd)
   structure CSet = RedBlackSetFn(ChainOrd)
   structure PSet = RedBlackSetFn(PairChainOrd)
      
   datatype ctx = Facts of ((chain * CSet.set) list) * (chain * chain) list
                | Bot
   type context = ctx * ctx
   
   val empty = (Facts ([],[]), Facts ([],[]))
   val bot =  (Bot, Bot)
   
   fun isBot (Bot, Bot) = true
     | isBot _ = false
   
   fun pp_ctx (Bot) = "_|_"
     | pp_ctx (Facts (al, dis)) = 
         let val neqs = String.concatWith ", " (map (fn (a,b) => pp_chain a ^ " != " ^ pp_chain b) dis)
             val eqs = String.concatWith ", " (map (fn (r, a) => 
                                                    String.concatWith "==" (map pp_chain (r::(CSet.listItems a)))) al)
         in "{" ^ eqs ^ " and " ^ neqs ^ "}" end
   fun pp_context (rt,rf) = 
      case isBot (rt,rf) of
         true => "_|_"
       | false => "\\r true: " ^ pp_ctx rt ^ " /\\ \\r false: " ^ pp_ctx rf   
   fun exp_deref e f =
      case e of 
         Gcl.Deref(e, _) => 
          (case expr_chain e of
              SOME c => SOME (f c)
            | NONE => NONE)
       | _ => NONE
   and expr_chain e =
      case e of 
         Gcl.Var (x,_) => SOME (Var x)
       | Gcl.Select(e, f, s) => exp_deref e (fn c => Field(c,f))
       | Gcl.Null _ => SOME (NullChain)
       | _ => NONE
   
   
   fun inDomain ctx e = 
     case e of
        Gcl.Rel(_, Gcl.Pointer _, a, b) => 
          (case (expr_chain a, expr_chain b) of
             (SOME _, SOME _) => true
           | _ => false)
      | _ => false
     
   
   fun ce c d = (ChainOrd.compare(c,d) = EQUAL)
   fun swapChain (a,b) = if ChainOrd.compare(a,b) = GREATER then (b,a) else (a,b)
   
   fun setFromList l = foldl CSet.add' CSet.empty l
   fun setToRepr s = 
      case CSet.listItems s of
         r::x::rest => SOME (r, foldl CSet.add' CSet.empty (x::rest))
       | [_] => NONE
       | [] => NONE
       
   local
      fun chnDomain (Var x) = SymSet.singleton x
        | chnDomain (Field(c,_)) = chnDomain c
        | chnDomain (NullChain) = SymSet.empty
      fun varDomain Bot = SymSet.empty
        | varDomain (Facts(al, dj)) = 
            let val chains = List.concat ((map (fn (r, c) => r::(CSet.listItems c)) al)
                                          @ (map (fn (a,b) => [a,b]) dj))
            in foldl SymSet.union SymSet.empty (map chnDomain chains) end
            
            
      
      fun renameCh mapping (Var x) = Var (case SymMap.find(mapping,x) of SOME x => x | _ => raise Fail "couldn't find var")
        | renameCh mapping (Field(c,f)) = Field(renameCh mapping c, f)
        | renameCh mapping (NullChain) = NullChain
      fun renameCtx mapping Bot = Bot
        | renameCtx mapping (Facts(al, dj)) = 
            let val al' = List.mapPartial (fn (r, c) => 
                                let val s = CSet.add(CSet.map (renameCh mapping) c, renameCh mapping r)
                                in setToRepr s end
                              ) al
                val dj' = map (fn (a,b) => swapChain(renameCh mapping a, renameCh mapping b)) dj
            in Facts(al', dj') end
   in
      fun ctxDomain (a,b) = SymSet.union(varDomain a, varDomain b)
      fun alphaRename ((ca,cb), formals) = 
         (* Note: ctxDomain context == formals*)
        let val formals' = (map (fn f => (f, Symbol.new(Symbol.name f))) formals)
            val mapping = foldl SymMap.insert' SymMap.empty formals'
        in ((renameCtx mapping ca, renameCtx mapping cb), map (#2) formals') end
   end
     
   
   fun aliasRepr' al c =
         case List.find (fn (r, s) => ce c r orelse CSet.member(s,c)) al of
            NONE => c
          | SOME (r, s) => r  
   fun aliasRepr al (Field(c,f)) = aliasRepr' al (Field(aliasRepr al c, f))
     | aliasRepr al x = aliasRepr' al x
   
   
   fun lub' (Bot) (a) = a
     | lub' (a) (Bot) = a
     | lub' (Facts (aal, adj)) (Facts (bal, bdj)) = 
       let val eqlists = map (fn (r, s) => r :: (CSet.listItems s)) aal
           val pairs = map (map (fn x => (aliasRepr bal x, x))) eqlists
           val groups = List.concat (map (AUtil.collect ChainOrd.compare) pairs)
           val sets = List.mapPartial (fn (r, l) => setToRepr(setFromList l)) groups
           fun newDisj aliases olddj =   
             let val members = foldl CMap.insert' CMap.empty (map (fn (r, s) => (r, r::(CSet.listItems s))) aliases)
                 fun handleDj (rA,rB) = 
                   let val (ma,mb) = (getOpt(CMap.find(members, rA), [rA]),
                                      getOpt(CMap.find(members, rB), [rB]))
                          
                   in foldl PSet.add' PSet.empty (List.concat (map (fn a => map (fn b => swapChain (aliasRepr sets a, aliasRepr sets b)) mb) ma)) end
             in foldl PSet.union PSet.empty (map handleDj olddj) end
           val disjoints = PSet.listItems(PSet.intersection(newDisj aal adj, newDisj bal bdj))
         (*val _ = AUtil.say ("lub' of " ^ (pp_ctx (Facts (aal, adj))) ^ "\n   with " ^(pp_ctx (Facts (bal, bdj))) ^ "\n   into " ^ (pp_ctx (Facts(sets, disjoints)))) *)
       in Facts(sets, disjoints) end
       
   fun glb' (Bot) (_) = Bot
     | glb' (_) (Bot) = Bot
     | glb' (Facts (aal, adj)) (Facts (bal, bdj)) =
         (* Take al and bl together. If they imply contradiction, glb' is bot.
            Otherwise, simplify the joined result and return it. *)
       let
       
         (*val _ = AUtil.say "glbing ..." *)
           val reprList = (List.concat (map (fn (r, s) => map (fn x => (x,r))
                                                              (CSet.listItems s))
                                            (aal @ bal)))
           fun trueRepr reprs (Field(c,f)) =
                 let val f = Field(trueRepr reprs c,f) in (case CMap.find(reprs, f) of 
                                                NONE => f
                                              | SOME r => trueRepr reprs r) end
             | trueRepr reprs x =(case CMap.find(reprs, x) of 
                                     NONE => x
                                   | SOME r => trueRepr reprs r)
           fun unionFindStep ((a, r), reprs) =
             let val reprA = trueRepr reprs a
                 val reprR = trueRepr reprs r
             in 
               if ChainOrd.compare (reprA,reprR) <> EQUAL then
                 CMap.insert(reprs, reprA, reprR)
               else reprs
             end
           
           (*val _ = AUtil.say "union find..."*)
           val reprs = foldl unionFindStep CMap.empty reprList
           
         (*val _ = AUtil.say "mapping..."
           val _ = AUtil.say (String.concatWith ", " (map (fn (k,ch) => (pp_chain k) ^ " -> " ^ (pp_chain ch)) (CMap.listItemsi reprs))) *)
           val reprsCompressed = CMap.map (trueRepr reprs) reprs (* Compress the reprs*)
           fun reprOf (Field(c,f)) = 
                        let val x = Field(reprOf c,f) in getOpt(CMap.find(reprs, x), x) end
             | reprOf x = getOpt(CMap.find(reprs, x), x)
             
           val contradict = List.exists (fn (a,b) => ce (reprOf a) (reprOf b)) (adj@bdj)
           val sets = List.mapPartial (fn (r, l) => setToRepr(setFromList (r::l)))
                                      (AUtil.collect ChainOrd.compare (map (fn (a,b)=>(b,a)) (CMap.listItemsi reprsCompressed)))
           val disjoints = ListMergeSort.uniqueSort PairChainOrd.compare 
                           (map (fn (a,b) => swapChain (aliasRepr sets a, aliasRepr sets b)) (adj@bdj))
                           
         (*val _ = AUtil.say "done." *)
       in case contradict of 
             true => Bot
           | false => Facts (sets, disjoints)
       end
            
   
   
   fun glb (a as (gt,gf), b as (gt',gf')) = 
     let (*val _ = AUtil.say ("before glb: " ^ pp_context a ^ " -- "^ pp_context b)*)
         val res = (glb' gt gt', glb' gf gf')
         (*val _ = AUtil.say ("after glb: " ^ pp_context res)*)
     in res end
   fun lub ((gt,gf), (gt',gf')) = (lub' gt gt', lub' gf gf')
   
   fun aliasesCtx (a,b) = let val (a,b) = swapChain (a,b) in Facts([(a,CSet.singleton b)], []) end
   fun disjointCtx (a,b) = Facts([], [swapChain(a,b)])
   
   fun learnFromEquality g (SOME a) (SOME b) = 
         glb (g, (aliasesCtx(a,b), aliasesCtx(a,b)))
     | learnFromEquality (rt,rf) _ _ = (rt,rf)
     
   fun learnFromDisequality g (SOME a) (SOME b) =  
         glb (g, (disjointCtx(a,b), disjointCtx(a,b)))
     | learnFromDisequality (rt,rf) _ _ = (rt,rf)
         
   local
   fun is_chain_outof _ (NullChain) = true
     | is_chain_outof (Modifies.ModUnion mods) c =  List.all (fn m => is_chain_outof m c) mods
     | is_chain_outof (Modifies.ModField f) (Field (c,f')) = Gcl.compareField (f,f') <> EQUAL
                                                             andalso is_chain_outof (Modifies.ModField f) c
     | is_chain_outof (Modifies.ModField f) _ = true
     | is_chain_outof (Modifies.ModVar v)    (Var v') = Symbol.compare (v, v') <> EQUAL
     | is_chain_outof (Modifies.ModVar v)    (Field (c,_)) = is_chain_outof (Modifies.ModVar v) c
     | is_chain_outof (Modifies.ModAnyField) (Field _) = false
     | is_chain_outof (Modifies.ModAnyField) _ = true
   in
     fun havoc' modifies Bot = Bot
       | havoc' modifies (Facts (al, dj)) = 
           let val outof = is_chain_outof modifies
               fun newClauseAndRepr (oldRepr, set) = 
                  let val oldSet = CSet.add(set, oldRepr) in    
                    case CSet.listItems (CSet.filter outof oldSet) of
                       [] => (NONE, NONE)
                     | r::[] => (SOME (oldRepr, r), NONE)
                     | r::rest => (SOME(oldRepr, r), 
                                   SOME(r, List.foldl CSet.add' CSet.empty rest))
                  
                  end
               val (mappingPairs, newClauses) = ListPair.unzip(List.map newClauseAndRepr al)
               val reprs = foldl CMap.insert' CMap.empty (List.mapPartial (fn x=>x) mappingPairs)
               fun newReprOf x =
                  case CMap.find(reprs, x) of 
                     NONE => if outof x then SOME x else NONE
                   | SOME x' => SOME x'
               val new_disj = List.mapPartial (fn (a,b) => 
                                                 case (newReprOf a, newReprOf b) of
                                                    (SOME a',SOME b') => SOME (a', b')
                                                  | _ => NONE ) dj
           in Facts(List.mapPartial (fn x=>x) newClauses, new_disj) end
     fun havoc modifies (t,f) =
     let (* val _ = AUtil.say ("before havoc: " ^ pp_context (t,f)) *)
         val res = (havoc' modifies t, havoc' modifies f)
         (* val _ = AUtil.say ("after havoc: " ^ pp_context res) *)
     in res end
     fun havocLocals locs ctx = havoc (Modifies.ModUnion(map Modifies.ModVar locs)) ctx
   end
   
   fun havocCall f gamma =
     if Purity.is_pure f then gamma
     else havoc (Modifies.lookup f) gamma
     
   structure FMap = SymMap
   val summaries = ref (FMap.empty : (context * Gcl.ident list) FMap.map)
   
   fun bindSummary f formals context =
     let  
          val toHavoc = SymSet.difference(ctxDomain context,
                                          foldl SymSet.add' SymSet.empty formals)
          val context' = havoc (Modifies.ModUnion (map Modifies.ModVar (SymSet.listItems toHavoc)))
                               context
          val _ = ()(*AUtil.say ("Summary for " ^ (Symbol.name f) ^ " = " ^ pp_context context')*)
     in 
       summaries := FMap.insert(!summaries, f, (context', formals))
     end
   fun chainFromField (p,f) = Field(Var p, f)
   fun chainFromVar p = Var p
   
   open Gcl
   
   fun applySummary ctx f args =
     case FMap.find(!summaries, f) of 
        NONE => (()(*AUtil.say ("warning: function not summarized " ^ (Symbol.name f))*); (ctx,ctx))
      | SOME (context, formals) =>
          let val ((sT, sF), formals') = alphaRename (context, formals)
              val ctx' = foldl (fn ((f,ch),c) => learnFromEquality c (SOME(chainFromVar f)) ch)
                         ctx (ListPair.zip (formals', args))
          in (glb (ctx', (sT, sT)), glb(ctx', (sF,sF))) end
          
   fun analyzeBoolExpr gamma exp = 
      case exp of 
         (* We don't track locals yet... *)
         Var (v, _) => if Symbol.compare (v, Trans.resultVar) = EQUAL then ((#1 gamma, Bot), (Bot, #2 gamma))
                       else (gamma, gamma)
       | ValOp (BoolConst true, []) => (gamma, bot)
       | ValOp (BoolConst false, []) => (bot, gamma)
       | ValOp (Not, [e]) =>
           let val (gt,gf) = analyzeBoolExpr gamma e in (gf, gt) end
       
       | ValOp (And, [e1, e2]) =>
            let val (t,f) = analyzeBoolExpr gamma e1
                val (t', f') = analyzeBoolExpr t e2
            in (t', lub (f, f')) end
       | ValOp (Or, [e1, e2]) =>
            let val (t, f ) = analyzeBoolExpr gamma e1
                val (t',f') = analyzeBoolExpr f e2
            in (lub (t, t'), f') end
       | ValOp (Cond, [c, a, b]) =>
           let val (ct, cf) = analyzeBoolExpr gamma c
               val (at, af) = analyzeBoolExpr ct a
               val (bt, bf) = analyzeBoolExpr cf b
            in (lub(at, bt), lub (af, bf)) end
       | ValOp (PureCall (f, Bool), args) => applySummary gamma f (map expr_chain args)
       | ValOp (oper, args) => (gamma, gamma)
       | Rel (Eq, Pointer _, e1, e2) => 
             (learnFromEquality gamma (expr_chain e1) (expr_chain e2),
              learnFromDisequality gamma (expr_chain e1) (expr_chain e2))
       | Rel (Neq, Pointer _, e1, e2) =>
             (learnFromDisequality gamma (expr_chain e1) (expr_chain e2),
              learnFromEquality gamma (expr_chain e1) (expr_chain e2))
       | Rel (r, Char, e1, e2) => (gamma, gamma)
       | Rel (r, Int, e1, e2) => (gamma, gamma)
       | Sub (a, i, tp) => (gamma, gamma)
       
       | Null tp => (gamma,gamma)
       | Select (e, f, tp) => (gamma,gamma)
       | Deref (e,tp) => (gamma,gamma)
   
   fun analyzeAssign gamma (lhs, rhs) = 
     let 
      (*val _ = AUtil.say ("\n  before " ^ (Gcl.pp_stmt (Gcl.Assign(lhs,rhs))) ^ ": " ^ pp_context gamma) *)
         val (gamma, rhs_chain) =
       case rhs of
          Expr e => (gamma, expr_chain e)
        | Alloc t =>
             let val sym = Symbol.new("$alloc")
                 val chain = SOME (chainFromVar sym)
                 val gamma' = learnFromDisequality gamma chain (SOME NullChain)
             in (gamma', chain) end
        | AllocArray (t, e) => (gamma, NONE)
        | Call (f,args) => (havocCall f gamma, NONE)
     val res =
       case lhs of 
           Local x =>
            (case (Symbol.compare(x, Trans.resultVar), rhs) of
               (EQUAL, Expr(ValOp(BoolConst true, []))) => (#1 gamma, Bot)
             | (EQUAL, Expr(ValOp(BoolConst false, []))) => (Bot, #2 gamma)
             | _ => 
                 let val g = havoc (Modifies.ModVar x) gamma
                 in learnFromEquality g (SOME (chainFromVar x)) rhs_chain end)
         | Field (p,f) => let val g = havoc (Modifies.ModField f) gamma in
             learnFromEquality g (SOME (chainFromField (p,f))) rhs_chain end
         | Cell p => gamma
         | ArrayElem (a,i) => gamma
     
      (*val _ = AUtil.say ("\n  after: " ^ pp_context res) *)
     in res end
end

structure NullityAnalysis = SafetyAnalysis(NullityContext)
