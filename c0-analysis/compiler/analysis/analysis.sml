(* C0 Compiler
 * SSA Analysis of well typed expressions
 * Jason Koenig <jrkoenig@andrew.cmu.edu>
 *)




signature ANALYSIS = 
sig
   val analyze: Ast.program -> AAst.afunc list
   val check: AAst.afunc list -> VError.error list
end

structure Analysis :> ANALYSIS =
struct
   
   structure Env = SSAEnvironment
   open AAst
   
   (* Label takes an environment and an expression, and produces an aexpr which
      annotates all local variables with their definitions in the environment.*)
   fun label env exp = 
      case exp of
            Ast.Var v => (case Env.lookup env v of
                             NONE => raise Fail ("unknown variable, internal bug: " ^ Symbol.name v)
                           | SOME i => Local (v,i))
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
          | Ast.Select(e, f) => Select(label env e, f)
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
       | Select(e, f) => Select (relabel rl e, f)
       | MarkedE e => MarkedE (Mark.map (relabel rl) e)
   (* the same as the above, except for statements instead of expressions. *)
   fun relabelStmt rl stmt = 
      case stmt of 
         Nop => stmt
       | Seq (a,b) => Seq(relabelStmt rl a, relabelStmt rl b)
       | Assert e => Assert(relabel rl e)
       | Annotation e => Annotation(relabel rl e)
       | Def (l, e) => Def(relabel rl l, relabel rl e)
       | Assign (lv, oper, rv) => Assign(relabel rl lv, oper, relabel rl rv)
       | Expr e => Expr(relabel rl e)
       | Break => stmt
       | Continue => stmt
       | PhiBlock _ => stmt
       | Return e => Return(case e of NONE => NONE
                                    | SOME e' => SOME (relabel rl e'))
       | If (e, s1, s2) => If(relabel rl e, relabelStmt rl s1, relabelStmt rl s2)
       | While (phis, guard, specs, s) =>
            While(phis, relabel rl guard, map (relabel rl) specs, relabelStmt rl s)
       | MarkedS s => MarkedS (Mark.map (relabelStmt rl) s)
       
   (* If the expression is just a local variable, retrieve it ignoring marking
      information, otherwise return NONE.*)
   fun getLocal exp =
       case exp of 
           Ast.Marked m => getLocal (Mark.data m)
         | Ast.Var v => SOME v
         | _ => NONE     
   fun ssaVarDecl (decls, env, r, b, c) =
      let fun s' (Ast.VarDecl(v, tp, SOME ex, _), (s,e, r, b, c)) =
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
                  (Def (label env' (Ast.Var v), label env e'), env', [], [], [])
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
     | ssa (Ast.Return NONE, env) = (Return NONE, Env.empty, [env], [], [])
     | ssa (Ast.Return (SOME e), env) =
                        (Return (SOME (label env e)), env, [env], [], [])
     | ssa (Ast.Break, env) = (Break, env, [], [env], [])
     | ssa (Ast.Continue, env) = (Continue, env, [], [], [env])
     | ssa (Ast.If(e, strue, sfalse), env) =
         let val (st, et, trets, tbrks, tconts) = ssa (strue, env)
             val (sf, ef, frets, fbrks, fconts) = ssa (sfalse, env)
             val (env', phis) = Env.mergeEnvs [et,ef]
         in
            (Seq(If ((label env e), st, sf), PhiBlock(phis)),
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
            (Seq(While(loopPhis, (label envdef e),
                       map (labelSpec envdef) specs, stm'),
                 PhiBlock endPhis)),
             envOverallExit, rets, [], [])
         end
     | ssa ((Ast.Exp e), env) = (Expr (label env e), env, [], [], [])
     | ssa ((Ast.Assert (e,_)), env) = (Assert (label env e), env, [], [], [])
     | ssa ((Ast.Anno annos), env) = (foldr (Seq) Nop (map (Annotation o (labelSpec env)) annos)
                                      , env, [], [], [])
     | ssa (stm,e) = raise UnsupportedConstruct ("ssa: "^(Ast.Print.pp_stm stm))
   
   (* SSA is messy, so this function cleans up afterwards. In particular, it
      removes empty PhiBlocks and redundant Seq/Nops. *)
   fun simplifySeq(stm: astmt): astmt = 
      case stm of
        Seq(a, b) =>(case (simplifySeq a, simplifySeq b) of
                        (Nop, b) => b
                      | (a, Nop) => a
                      | (a, b) => Seq(a,b))
       | If(e, a, b) => If(e, simplifySeq a, simplifySeq b)
       | While(ph, e, specs, a) => While(ph, e, specs, simplifySeq a)
       | Nop => Nop
       | Assert _ => stm
       | Annotation _ => stm
       | Def _ => stm
       | Assign _ => stm
       | Expr _ => stm
       | PhiBlock [] => Nop
       | PhiBlock _ => stm
       | Return _ => stm
       | Continue => stm
       | Break => stm
       | MarkedS s => MarkedS (Mark.map simplifySeq s)
   
   fun analyzeArgs ctx args = 
      let fun aarg (Ast.VarDecl (id, tp, init, ext)) = 
         (id, tp, (id, valOf(Env.lookup ctx id)))
         (* all arguments should be assigned locals, valOf safe. *)
      in map aarg args end
   fun analyzeFunc (Ast.Function(name, rtp, args, SOME stmt, specs, false, ext)) = 
          let
             val () = Env.reset()
             val (stmt',types) = Preprocess.preprocess
                 (Ast.Function(name, rtp, args,
                               SOME (Ast.Markeds (Mark.mark' (stmt, ext))),
                               specs, false, ext))
             val (_, initialEnv, _, _, _) = ssaVarDecl (args, Env.empty, [], [], [])
             val args = analyzeArgs initialEnv args
             val reqs = List.filter (fn Ast.Requires _ => true | _ => false) specs
             val ens = List.filter (fn Ast.Ensures _ => true | _ => false) specs
             
             val reqs' = map (labelSpec initialEnv) reqs
             val ens' = map (labelSpec initialEnv) ens
             val (s, env, rets, _, _) = ssa (stmt', initialEnv)
             val s' = simplifySeq s
             val (errs) = NullityAnalysis.checkFunc rtp types reqs' s' ens'
            
          in
             [Function(rtp, types, args, reqs', s', ens')]
          (*["requires:"]@(map AAst.Print.pp_aexpr reqs')@
             ["ensures:"]@(map AAst.Print.pp_aexpr ens')@
             [(Ast.Print.pp_tp rtp) ^ " " ^ (Symbol.name name)
                  ^ "(args)\n{\n" ^ (AAst.Print.pp_astmt s') ^"\n}"]@
             (map (VError.pp_error) (errs))
          *)
          end 
     | analyzeFunc _ = []
   fun checkFunc (Function(rtp, types, formals, reqs, s, ens)) =
      NullityAnalysis.checkFunc rtp types reqs s ens
   
   fun analyze prog = List.concat (map analyzeFunc prog)
   fun check funcs = List.concat (map checkFunc funcs)
end


