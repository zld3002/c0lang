(* C0 Compiler
 * SSA Analysis of well typed expressions
 * Jason Koenig <jrkoenig@andrew.cmu.edu>
 *)

signature ANALYSIS = 
sig
   val analyze: bool -> Ast.program -> AAst.afunc list
end

structure Analysis :> ANALYSIS =
struct
   
   structure Env = SSAEnvironment
   open AAst
   
   val typeContext = ref (Symbol.empty: Ast.tp Symbol.table)
   fun labelVar env v =
     case Env.lookup env v of
        NONE => raise Fail ("unknown variable, internal bug: " ^ Symbol.name v)
      | SOME i => (v,i)
   (* Label takes an environment and an expression, and produces an aexpr which
      annotates all local variables with their definitions in the environment.*)
   fun label env exp = 
      case exp of
            Ast.Var v => Local(labelVar env v)
          | Ast.OpExp(oper, el) => Op(oper, map (label env) el)
          | Ast.FunCall(f, el) => Call(f, map (label env) el)
          | Ast.Marked m => MarkedE (Mark.mark' (label env (Mark.data m), Mark.ext m))
          | Ast.IntConst n => IntConst n
          | Ast.True => BoolConst true
          | Ast.False => BoolConst false
          | Ast.StringConst s => StringConst s
          | Ast.CharConst c => CharConst c
          | Ast.Old e => Old(label env e)
          | Ast.Length e => Length(label env e)
          | Ast.Result => Result
          | Ast.Null => Null
          | Ast.Alloc(tp) => Alloc(tp)
          | Ast.Select(e, f) =>
              let val Ast.StructName s = Syn.expand_def (Syn.syn_exp (!typeContext) e)
              in Select(label env e, s, f) end
          | Ast.AllocArray(tp, e) => AllocArray(tp, label env e)
          (*| _ => raise UnsupportedConstruct ("label: " ^ (Ast.Print.pp_exp exp))*)
   (* the same as the above, except will strip the annotation category (requires,
      ensures, etc.) off, then label. *)
   fun labelSpec env spec =
      case spec of
         Ast.Requires (e, ext) => MarkedE (Mark.mark' (label env e, ext))
       | Ast.Ensures (e, ext) => MarkedE (Mark.mark' (label env e, ext))
       | Ast.LoopInvariant (e, ext) => MarkedE (Mark.mark' (label env e, ext))
       | Ast.Assertion (e, ext) => MarkedE (Mark.mark' (label env e, ext))
   (* given a map from Locals to ints (rl), replace any local in the domain of
      rl with the same symbol, but the SSA index from the map. *)
   fun relabel rl exp = 
      case exp of 
         Local (v,i) => (case LocalMap.find (rl, (v,i)) of 
                           SOME j => Local (v,j)
                         | NONE => Local (v,i))
       | Op (oper, l) => Op(oper, map (relabel rl) l)
       | Call (f, l) => Call(f, map (relabel rl) l)
       | IntConst _ => exp
       | BoolConst _ => exp
       | StringConst _ => exp
       | CharConst _ => exp
       | Alloc _ => exp
       | Null => exp
       | Result => exp
       | Length (e) => Length (relabel rl e)
       | Old (e) => Old (relabel rl e)
       | AllocArray (tp, e) => AllocArray(tp, relabel rl e)
       | Select(e, s, f) => Select (relabel rl e, s, f)
       | MarkedE e => MarkedE (Mark.map (relabel rl) e)
   (* the same as the above, except for statements instead of expressions. *)
   fun relabelStmt rl stmt = 
      case stmt of 
         Nop => stmt
       | Seq (a,b) => Seq(relabelStmt rl a, relabelStmt rl b)
       | Assert e => Assert(relabel rl e)
       | Error e => Error(relabel rl e)
       | Annotation e => Annotation(relabel rl e)
       | Def ((v,i), e) => Def(
                       (case LocalMap.find (rl, (v,i)) of 
                           SOME j => (v,j)
                         | NONE => (v,i)), relabel rl e)
       | Assign (lv, oper, rv) => Assign(relabel rl lv, oper, relabel rl rv)
       | Expr e => Expr(relabel rl e)
       | Break => stmt
       | Continue => stmt
       | Return e => Return(case e of NONE => NONE
                                    | SOME e' => SOME (relabel rl e'))
       | If (e, s1, s2, phis) => If(relabel rl e, relabelStmt rl s1, relabelStmt rl s2, phis)
       | While (phis, guard, specs, mods, s, endphis) =>
            While(phis, relabel rl guard, map (relabel rl) specs, mods, relabelStmt rl s, endphis)
       | MarkedS s => MarkedS (Mark.map (relabelStmt rl) s)
       
   (* If the expression is just a local variable, retrieve it ignoring marking
      information, otherwise return NONE.*)
   fun getLocal exp =
       case exp of 
           Ast.Marked m => getLocal (Mark.data m)
         | Ast.Var v => SOME v
         | _ => NONE     
   fun ssaVarDecl (decls, env, r, b, c) =
      let fun s' (Ast.VarDecl(v, tp, SOME ex, _), (s, e, r, b, c)) =
                      let val (sp, ep, _, _, _) = ssa (Ast.Assign(NONE, Ast.Var v, ex), e)
                      in (Seq(s, sp), ep, r, b, c) end
            | s' (Ast.VarDecl(v, tp, NONE, _), (s,e, r, b, c)) =
                      let val e' = Env.inc e v in
                      (s, e', r, b, c)
                      end
      in foldl s' (Nop, env, r, b, c) decls end
   (* The main ssa calculation function.
      ssa: Ast.stm * Env.env -> (astmt * env * env list * env list * envlist)
      ssa (stmt, env) = (stmt', returns, breaks, continues)
         where stmt is the statement to analyze in environment env
               stmt' is the annotated, SSA form
               env' is the enviornment after the statement executes (note that
                    for non-local control flow, this may be empty.
               returns are the environments at any return statement
               breaks are the environments at any uncaught break
               continues are the environments at any uncaught continue statement.
      *)
   and ssa ((Ast.Assign (oper, var, e)), env)= 
         (case getLocal var of
             NONE => (Assign(label env var, oper, label env e), env, [], [], [])
           | SOME v => 
               let val env' = Env.inc env v
                   val e' = case oper of
                              SOME oper' => Ast.OpExp(oper', [Ast.Var v, e])
                            | NONE => e
               in
                  (Def (labelVar env' v, label env e'), env', [], [], [])
               end)
     | ssa (Ast.Markeds m, env) = 
         let val (stmt, env', r, b, c) = ssa (Mark.data m, env)
         in (MarkedS (Mark.mark' (stmt, Mark.ext m)), env', r, b, c) end
     | ssa (Ast.Seq ([], sl), env) = 
         let fun ssa' (stm, (s, e, r, b, c)) = 
             let val (s', e', r', b', c') = ssa (stm, e) in (Seq(s,s'), e', r@r', b@b', c@c') end
         in foldl ssa' ((Nop, env, [], [], [])) sl end
     | ssa (Ast.Seq _, env) = raise Fail "preprocessor error"
     | ssa (Ast.StmDecl decl, env) = (ssaVarDecl ([decl], env, [], [], []))
     | ssa (Ast.Return NONE, env) = (Return NONE, env, [env], [], [])
     | ssa (Ast.Return (SOME e), env) =
                        (Return (SOME (label env e)), env, [env], [], [])
     | ssa (Ast.Break, env) = (Break, env, [], [env], [])
     | ssa (Ast.Continue, env) = (Continue, env, [], [], [env])
     | ssa (Ast.If(e, strue, sfalse), env) =
         let val (st, et, trets, tbrks, tconts) = ssa (strue, env)
             val (sf, ef, frets, fbrks, fconts) = ssa (sfalse, env)
             val (env', phis) = Env.mergeEnvs [et,ef]
         in
            (If ((label env e), st, sf, phis),
                 env', trets @ frets, tbrks @ fbrks, tconts @ fconts)
         end
     | ssa (Ast.While(e, specs, stm), env) =
         let val envdef = Env.incAll env
             val (stm', env', rets, brks, conts) = ssa (stm, envdef)
             val (envExit, loopPhis, relabeling) = 
                     Env.mergeEnvsLoop envdef ([env, env'] @ conts)
             val (envOverallExit, endPhis) = Env.mergeEnvs ([envExit] @ brks)
         in
            (relabelStmt relabeling
            (While(loopPhis, (label envdef e),
                       map (labelSpec envdef) specs, ModAnything, stm',endPhis)),
             envOverallExit, rets, [], [])
         end
     | ssa ((Ast.Exp e), env) = (Expr (label env e), env, [], [], [])
     | ssa ((Ast.Assert (e,_)), env) = (Assert (label env e), env, [], [], [])
     | ssa ((Ast.Error e), env) = (Error (label env e), env, [], [], [])
     | ssa ((Ast.Anno annos), env) = (foldr (Seq) Nop (map (Annotation o (labelSpec env)) annos)
                                      , env, [], [], [])
     | ssa (stm,e) = raise UnsupportedConstruct ("ssa: "^(Ast.Print.pp_stm stm))
   
   (* SSA is messy, so this function cleans up afterwards. In particular, it
      removes redundant Seq/Nops. *)
   fun simplifySeq(stm: astmt): astmt = 
      case stm of
        Seq(a, b) =>(case (simplifySeq a, simplifySeq b) of
                        (Nop, b) => b
                      | (a, Nop) => a
                      | (a, b) => Seq(a,b))
       | If(e, a, b, p) => If(e, simplifySeq a, simplifySeq b, p)
       | While(p, e, specs, mods, a, p') => While(p, e, specs, mods, simplifySeq a, p')
       | Nop => Nop
       | Assert _ => stm
       | Error _ => stm
       | Annotation _ => stm
       | Def _ => stm
       | Assign _ => stm
       | Expr _ => stm
       | Return _ => stm
       | Continue => stm
       | Break => stm
       | MarkedS s => MarkedS (Mark.map simplifySeq s)
   
   local 
     structure S = LocalSet
   in
     fun usedE e =
        case e of
           Local l => S.singleton l
         | Op (oper, args) => foldl S.union S.empty (map usedE args)
         | Call(f, args) => foldl S.union S.empty (map usedE args)
         | IntConst _ => S.empty
         | BoolConst _ => S.empty
         | StringConst _ => S.empty
         | CharConst _ => S.empty
         | Alloc _ => S.empty
         | Null => S.empty
         | Result => S.empty
         | Length (e) => usedE e
         | Old (e) => usedE e
         | AllocArray (tp, e) => usedE e
         | Select (e, s, f) => usedE e
         | MarkedE m => usedE (Mark.data m)
     fun usedP' (PhiDef(s,i,l)) =
        S.addList (S.empty, map (fn j => (s,j)) l)
     fun usedP l = foldl S.union S.empty (map usedP' l)
     fun usedS s =
        case s of 
           Nop => S.empty
         | Seq (a,b) => S.union(usedS a, usedS b)
         | Assert e => usedE e
         | Error e => usedE e
         | Annotation e => usedE e
         | Def (l, e) => usedE e
         | Assign (lv, oper, e) => S.union(usedE lv, usedE e)
         | Expr e => usedE e
         | Break => S.empty
         | Continue => S.empty
         | Return (NONE) => S.empty
         | Return (SOME e) => usedE e
         | If (e,a,b,p) =>
             S.union(usedE e, S.union(usedS a, S.union(usedS b, usedP p)))
         | While (p, e, invs, mods, b, p') =>
             let val i = foldl S.union S.empty (map usedE invs)
             in S.union(usedE e, S.union(i, S.union(usedS b, usedP (p@p'))))
             end
         | MarkedS m => usedS (Mark.data m)
         
         
     fun simplifyPhiP ctx phis =
       let fun used (PhiDef(s,i,_)) = S.member(ctx, (s,i))
       in (List.filter used phis, not(List.all (used) phis)) end
     fun simplifyPhiS' ctx stm = 
        case stm of 
           Seq(a, b) => 
             let val (a', ca) = simplifyPhiS' ctx a
                 val (b', cb) = simplifyPhiS' ctx b
             in (Seq(a', b'), ca orelse cb) end
         | If(e, a, b, p) =>
             let val (a', ca) = simplifyPhiS' ctx a
                 val (b', cb) = simplifyPhiS' ctx b
                 val (p', cp) = simplifyPhiP ctx p
             in (If(e, a', b', p'), ca orelse cb orelse cp) end
         | While(pb, e, invs, mods, b, pe) =>
             let val (pb', cpb) = simplifyPhiP ctx pb
                 val (pe', cpe) = simplifyPhiP ctx pe
                 val (b', cb) = simplifyPhiS' ctx b
             in (While(pb', e, invs, mods, b', pe'), cpb orelse cpe orelse cb) end
         | Nop => (stm, false)
         | Assert _ => (stm, false)
         | Error _ => (stm, false) (* Is this right? -rjs Dec 8 2012 *)
         | Annotation _ => (stm, false)
         | Def _ => (stm, false)
         | Assign _ => (stm, false)
         | Expr _ => (stm, false)
         | Return _ => (stm, false)
         | Continue => (stm, false)
         | Break => (stm, false)
         | MarkedS m =>
             let val (stm', c) = simplifyPhiS' ctx (Mark.data m)
             in (MarkedS (Mark.mark'(stm',Mark.ext m)),c) end
     fun simplifyPhiS stm =
       let val ctx = usedS stm
           val (stm', changed) = simplifyPhiS' ctx stm
       in
         case changed of
            true => simplifyPhiS stm'
          | false => stm'
       end
   end
   fun analyzeArgs ctx args = 
      let fun aarg (Ast.VarDecl (id, tp, init, ext)) = 
         (id, tp, (id, valOf(Env.lookup ctx id)))
         (* all arguments should be assigned locals, valOf safe. *)
      in map aarg args end
   fun analyzeFunc iso (Ast.Function(name, rtp, args, SOME stmt, specs, false, ext)) = 
          let
             val () = Env.reset()
             val (stmt',types) = Preprocess.preprocess iso
                 (Ast.Function(name, rtp, args,
                               SOME (Ast.Markeds (Mark.mark' (stmt, ext))),
                               specs, false, ext))
             (* val _ = typeContext := Symbol.digest (SymMap.listItemsi types) *)
             val _ = typeContext := Symbol.digest (SymMap.listItemsi (SymMap.insert(types, Symbol.symbol "\\result", rtp)))
             val (_, initialEnv, _, _, _) = ssaVarDecl (args, Env.empty, [], [], [])
             val args = analyzeArgs initialEnv args
             val reqs = List.filter (fn Ast.Requires _ => true | _ => false) specs
             val ens = List.filter (fn Ast.Ensures _ => true | _ => false) specs
             
             val reqs' = map (labelSpec initialEnv) reqs
             val ens' = map (labelSpec initialEnv) ens
             val (s, env, rets, _, _) = ssa (stmt', initialEnv)
             val s' = simplifySeq s
             val s'' = simplifyPhiS s'
          in
             [Function(rtp, name, types, args, reqs', s'', ens')]
          end 
     | analyzeFunc iso _ = []
   
   fun analyze iso prog = List.concat (map (analyzeFunc iso) prog)
end


