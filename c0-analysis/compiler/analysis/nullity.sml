
(* The four element lattice representing a single variable's nullity
   information. *)
structure NullityLattice = 
struct
   datatype lat = Top | Bot | Null | NotNull
   fun lub Top _ = Top
     | lub _ Top = Top
     | lub Bot b = b
     | lub a Bot = a
     | lub Null NotNull = Top
     | lub NotNull Null = Top
     | lub NotNull NotNull = NotNull
     | lub Null Null = Null
     
   fun glb Bot _ = Bot
     | glb _ Bot = Bot
     | glb Top b = b
     | glb a Top = a
     | glb Null NotNull = Bot
     | glb NotNull Null = Bot
     | glb NotNull NotNull = NotNull
     | glb Null Null = Null
     
   fun neg Top = Bot
     | neg Bot = Top
     | neg Null = NotNull
     | neg NotNull = Null
   fun pp_lat Top = "T"
     | pp_lat Null = "!"
     | pp_lat NotNull = "&"
     | pp_lat Bot = "_|_"
end

(* A CONTEXT which tracks only nullity information about local variables. *)
structure NullityContext :> CONTEXT =
struct
   structure NL = NullityLattice
   type context = NL.lat LocalMap.map
        (*map locals to their lattice types, but only if they are pointer type *)
   
   open VError
   
   val empty = LocalMap.empty
   val bot =  LocalMap.insert (empty, (Symbol.new "_", 0), NL.Bot)
   
   fun singleContext l elt = 
      LocalMap.insert (empty, l, elt)
   
   fun isBot g = LocalMap.foldr (fn (elt, b) => b orelse elt = NL.Bot) false g
   
   fun pp_context gamma = 
      case isBot gamma of
         true => "{_|_}"
       | false =>
      "{" ^ (AAst.Print.commas "; " 
               (map (fn (l, tp) => (AAst.Print.pp_aexpr (AAst.Local l)) ^ " => " ^ (NL.pp_lat tp))
                    (LocalMap.listItemsi gamma))) ^ "}"
    
   val result = (Symbol.new "\\result", 0)
   fun getLat gamma l =
      case LocalMap.find (gamma, l) of                            
         NONE => NL.Top
       | SOME e => e
   fun glb (g, g') = 
       LocalMap.unionWith (fn (x,y) => NL.glb x y) (g,g')
   (* FIXME: this is wrong. the issue is that if you are given something like 
      if( * ) n`1 := alloc else n`2 := alloc} n`3 := phi(n`1,n`2),
      you want to be able to say that between the the if and the phi, n`1 is
      not null and so is n`2, so when the phi comes along they get merged properly.
      however, under the current code, while loops break.*)
   fun lub (g, g') =
       case (isBot g, isBot g') of
          (true, _) => g'
        | (_, true) => g
        | _ => LocalMap.intersectWith (fn (x,y) => NL.lub x y) (g, g')
     
   fun exp_lat gamma e = 
      case e of
         AAst.Alloc _ => NL.NotNull
       | AAst.AllocArray _ => NL.NotNull                     
       | AAst.Local l => getLat gamma l
       | AAst.Null => NL.Null
       | AAst.Result => getLat gamma result
       | AAst.MarkedE m => exp_lat gamma (Mark.data m)
       | _ => NL.Top
       
       
   (* add the fact that e has type elt to the context gamma. only useful
      if we have a local, or a null. *)
   fun learnFromFact gamma e elt = 
      case e of
         AAst.Local l => glb (gamma, (singleContext l elt))
       | AAst.Null => (case elt of (*FIXME this is a hack...*)
                          NL.Top => gamma
                        | NL.Null => gamma
                        | NL.Bot => bot
                        | NL.NotNull => bot)
       | AAst.MarkedE m => learnFromFact gamma (Mark.data m) elt
       | _ => gamma
       
   (* given that the comparison a == b is true,
      add the facts we learn to the context*)
   fun learnFromEquality gamma a b = 
         let val aelt = exp_lat gamma a
             val belt = exp_lat gamma b
             val overall = NL.glb aelt belt
         in learnFromFact (learnFromFact gamma a overall) b overall end
         
   (* given that the comparison a != b is true,
      add the facts we learn to the context*)
   fun learnFromDisequality gamma a b = 
         let val aelt = exp_lat gamma a
             val belt = exp_lat gamma b
         in case (aelt, belt) of
               (NL.Null, _) => learnFromFact gamma b NL.NotNull
             | (_, NL.Null) => learnFromFact gamma a NL.NotNull
             | _ => gamma
         end
   
   fun proveEquality gamma (ext, a, b) =
     let val aelt = exp_lat gamma a
         val belt = exp_lat gamma b
     in 
       if (aelt = NL.Null orelse belt = NL.Null)
          then
          if (aelt = belt) then []
          else [VerificationError (ext, "could not prove equality")]
       else []
     end
     
   fun proveDisequality gamma (ext, a, b) =
     let val aelt = exp_lat gamma a
         val belt = exp_lat gamma b
     in if (NL.glb aelt belt) = NL.Bot
        then []
        else [VerificationError (ext, "could not prove inequality")]
     end
   
   
   fun analyzeExpr types gamma (ext, e) =
      case e of
         AAst.Local _ => ([],gamma)
       | AAst.IntConst _ => ([],gamma)
       | AAst.BoolConst _ => ([],gamma)
       | AAst.StringConst _ => ([],gamma)
       | AAst.CharConst _ => ([],gamma)
       | AAst.Alloc _ => ([],gamma)
       | AAst.AllocArray (tp, e) => analyzeExpr types gamma (ext, e)
       | AAst.Null => ([],gamma)
       | AAst.Result => ([],gamma)
       | AAst.Length(e) => analyzeExpr types gamma (ext, e)
       | AAst.Old(e) => analyzeExpr types gamma (ext, e)
       | AAst.Select(e, f) => analyzeExpr types gamma (ext, e)
       | AAst.Call (f, args) => 
           let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) args
           in (List.concat errs,gamma) end
       | AAst.Op (Ast.DEREF, [a]) => 
           (case exp_lat gamma a of
               NL.Top => [VerificationError (ext, "unprotected dereference "
                                                     ^ (AAst.Print.pp_aexpr e))]
             | NL.Null => [VerificationError (ext, "null dereference "
                                                     ^ (AAst.Print.pp_aexpr e))]
             | _ => [], gamma)
       | AAst.Op (oper, args) => (* FIXME: this is plain wrong if we have a boolean*)
           let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) args in (List.concat errs, gamma) end
       | AAst.MarkedE me => analyzeExpr types gamma (Mark.ext me, Mark.data me)
   

   
   (* computes (G', G'') corresponding to the judgements G; exp true |> G'
      and G; exp false |> G'', where G = gamma. *)
   fun analyzeBoolExpr types gamma (ext, exp) = 
      case exp of 
         AAst.BoolConst true => ([], gamma, bot)
       | AAst.BoolConst false => ([], bot, gamma)
       | AAst.Local _ => ([], gamma, gamma) (*right now we have no information from
                                          booleans.*)
       | AAst.Op(Ast.LESS, a) =>
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma, gamma) end
       | AAst.Op(Ast.LEQ, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma, gamma) end
       | AAst.Op(Ast.GREATER, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma, gamma) end
       | AAst.Op(Ast.GEQ, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma, gamma) end
       | AAst.Call (name, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma, gamma) end
       | AAst.Op(Ast.EQ, [a,b]) => 
            let val (e, _) = analyzeExpr types gamma (ext,a)
                val (e', _) = analyzeExpr types gamma (ext,b)
            in (e @ e', learnFromEquality gamma a b,
                        learnFromDisequality gamma a b) end
       | AAst.Op(Ast.NOTEQ, [a,b]) => 
            let val (e, _) = analyzeExpr types gamma (ext, a)
                val (e',_) = analyzeExpr types gamma (ext, b)
            in (e @ e', learnFromDisequality gamma a b,
                        learnFromEquality gamma a b) end
       | AAst.Op(Ast.LOGNOT, [a]) =>
            let val (e,t,f) = analyzeBoolExpr types gamma (ext,a) in (e,f,t) end
       | AAst.Op(Ast.LOGAND, [a,b]) => 
            let val (e,t,f) = analyzeBoolExpr types gamma (ext, a)
                val (e',t', f') = analyzeBoolExpr types t (ext, b)
            in (e @ e', t', lub (f, f')) end
       | AAst.Op(Ast.LOGOR, [a,b]) => 
            let val (e,t,f) = analyzeBoolExpr types gamma (ext, a)
                val (e',t',f') = analyzeBoolExpr types f (ext, b)
            in (e @ e', lub (t, t'), f') end
       | AAst.Op(Ast.DEREF, [a]) =>
           let val (e, gamma') = analyzeExpr types gamma (ext, a)
           in (e, gamma', gamma') end
       | AAst.Op(Ast.SUB, [a,b]) =>
           let val (e, gamma') = analyzeExpr types gamma (ext, a)
               val (e, gamma'') = analyzeExpr types gamma' (ext, b)
           in (e, gamma'', gamma'') end
       | AAst.Select(e, f) => 
           let val (err, gamma') = analyzeExpr types gamma (ext, e)
           in (err, gamma', gamma') end
       | AAst.Op(Ast.COND, [c, a, b]) =>
           let val (e, ct, cf) = analyzeBoolExpr types gamma (ext, c)
               val (e', at, af) = analyzeBoolExpr types ct (ext, a)
               val (e', bt, bf) = analyzeBoolExpr types cf (ext, b)
            in (e @ e', lub(at, bt), lub (af, bf)) end
       | AAst.MarkedE me => analyzeBoolExpr types gamma (Mark.ext me, Mark.data me)
       | AAst.Result => ([], gamma, gamma)
       | _ => raise Fail ("domain is bool-typed expressions only. bad: " ^ (AAst.Print.pp_aexpr exp))

   fun proveBoolExpr types gamma (ext, exp) tf = 
      case exp of 
         AAst.BoolConst const => 
           (case tf = const of
               true => ([], gamma)
             | false => ([VerificationError (ext,
                      "could not prove expression " ^ (AAst.Print.pp_aexpr exp) ^ (if tf then " to be true" else " to be false"))], bot))
       | AAst.Local _ => ([], gamma) (* no info from booleans yet. *)
       | AAst.Op(Ast.LESS, a) =>
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma) end
       | AAst.Op(Ast.LEQ, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma) end
       | AAst.Op(Ast.GREATER, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma) end
       | AAst.Op(Ast.GEQ, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma) end
       | AAst.Call (name, a) => 
            let val errs = map (fn a => #1(analyzeExpr types gamma (ext, a))) a
            in (List.concat errs, gamma) end
       | AAst.Op(Ast.EQ, [a,b]) => 
            let val (e, _) = analyzeExpr types gamma (ext,a)
                val (e',_) = analyzeExpr types gamma (ext,b)
                val (e'') = (if tf then proveEquality
                                 else proveDisequality) gamma (ext, a, b)
            in (e @ e' @ e'',(if tf then learnFromEquality
                              else learnFromDisequality) gamma a b) end
       | AAst.Op(Ast.NOTEQ, [a,b]) => 
            let val (e,_) = analyzeExpr types gamma (ext,a)
                val (e',_) = analyzeExpr types gamma (ext,b)
                val (e'') = (if tf then proveDisequality
                                 else proveEquality) gamma (ext, a, b)
            in (e @ e' @ e'', (if tf then learnFromDisequality
                               else learnFromEquality) gamma a b) end
       | AAst.Op(Ast.LOGNOT, [a]) =>
            proveBoolExpr types gamma (ext, a) (not tf)
       | AAst.Op(Ast.LOGAND, [a,b]) => 
          (case tf of
              true => let val (e,t) = proveBoolExpr types gamma (ext, a) tf
                          val (e',t') = proveBoolExpr types t (ext, b) tf
                      in (e @ e', t') end
            | false => let val (e,t,f) = analyzeBoolExpr types gamma (ext, a)
                           val (e',f') = proveBoolExpr types t (ext, b) tf
                       in (e @ e', lub (f, f')) end)
       | AAst.Op(Ast.LOGOR, [a,b]) => 
          (case tf of
              true => let val (e,t,f) = analyzeBoolExpr types gamma (ext, a)
                          val (e',t') = proveBoolExpr types f (ext, b) tf
                      in (e @ e', lub (t, t')) end
            | false => let val (e,f) = proveBoolExpr types  gamma (ext, a) tf
                           val (e',f') = proveBoolExpr types f (ext, b) tf
                       in (e @ e', f') end)
       | AAst.Op(Ast.DEREF, [a]) =>
           let val (e, gamma') = analyzeExpr types gamma (ext, a)
           in (e, gamma') end
       | AAst.MarkedE me => proveBoolExpr types gamma (Mark.ext me, Mark.data me) tf
       (* TODO: handle boolean arrays, i.e. the sub operator. *)
       | _ => raise Fail ("domain is bool-typed expressions only. bad: " ^ (AAst.Print.pp_aexpr exp))
    
   fun analyzePhi types g (AAst.PhiDef(v,i,l)) =
         glb (g, (singleContext (v,i)
                      (foldr (fn (a,b) => NL.lub a b) NL.Bot
                             (map (fn i' => getLat g (v,i')) l))))
   fun analyzePhi' types g (AAst.PhiDef(v,i,l)) j =
         LocalMap.insert(g, (v,i), getLat g (v, List.nth (l, j)))
   fun havocPhi types g (AAst.PhiDef(v,i,l)) =
               lub (g, (singleContext (v,i) NL.Top))
   fun isPointerLocal types (sym, i) =
      case SymMap.find (types, sym) of
         NONE => raise Fail "local not in type map?"
       | SOME tp => (case tp of Ast.Pointer _ => true | _ => false)
   
   fun analyzeDef types gamma (ext, AAst.Local l, e) =  
      let val (err, gamma') = analyzeExpr types gamma (ext, e)
      in if isPointerLocal types l
         then (err, glb (gamma', (singleContext l (exp_lat gamma e))))
         else (err, gamma') end
     | analyzeDef _ _ _ = raise AAst.UnsupportedConstruct "analyzeDef must take a local"
   
   fun analyzeReturn rtp types gamma (ext, e) =  
      let val (err, gamma') = analyzeExpr types gamma (ext, e)
      in
      case rtp of
         Ast.Pointer _ => (err, glb (gamma', (singleContext result (exp_lat gamma e))))
       | _ => (err, gamma')
      end
end


structure NullityAnalysis = SafetyAnalysis(NullityContext)
