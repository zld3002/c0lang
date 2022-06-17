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
          | Ast.AddrOf(f) => AddrOf(f)
          | Ast.Invoke(e, el) => Invoke(label env e, map (label env) el)
          | Ast.Marked m => MarkedE (Mark.mark' (label env (Mark.data m), Mark.ext m))
          | Ast.IntConst n => IntConst n
          | Ast.True => BoolConst true
          | Ast.False => BoolConst false
          | Ast.StringConst s => StringConst s
          | Ast.CharConst c => CharConst c
          | Ast.Hastag(tp, e) => Hastag(tp, label env e)
          | Ast.Length e => Length(label env e)
          | Ast.Result => Result
          | Ast.Null => Null
          | Ast.Alloc(tp) => Alloc(tp)
          | Ast.Select(e, f) =>
              let val Ast.StructName s = Syn.expand_def (Syn.syn_exp (!typeContext) e)
              in Select(label env e, s, f) end
          | Ast.AllocArray(tp, e) => AllocArray(tp, label env e)
          | Ast.Cast(tp, e) => Cast(tp, label env e)
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
       | AddrOf(f) => AddrOf(f)
       | Invoke (e, el) => Invoke (relabel rl e, map (relabel rl) el)
       | IntConst _ => exp
       | BoolConst _ => exp
       | StringConst _ => exp
       | CharConst _ => exp
       | Alloc _ => exp
       | Null => exp
       | Result => exp
       | Length (e) => Length (relabel rl e)
       | Hastag (tp, e) => Hastag (tp, relabel rl e)
       | AllocArray (tp, e) => AllocArray(tp, relabel rl e)
       | Cast(tp, e) => Cast(tp, relabel rl e)
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
                      let val e' = Env.inc e v 
                          val _ = print ("Var Decl: " ^ (Env.toString e') ^ "\n")              
                          val _ = print "==================\n"
                      in (s, e', r, b, c) end
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
             val _ = print ("IF MergeEnv: " ^ (Env.toString env') ^ "\n")
         in
            (If ((label env e), st, sf, phis),
                 env', trets @ frets, tbrks @ fbrks, tconts @ fconts)
         end
     | ssa (Ast.While(e, specs, stm), env) =
         let val envdef = Env.incAll env
             val (stm', env', rets, brks, conts) = ssa (stm, envdef)
             val (envExit, loopPhis, relabeling) = 
                     Env.mergeEnvsLoop envdef ([env, env'] @ conts)
             val _ = print ("WHILE MergeEnvExit: " ^ (Env.toString envExit) ^ "\n")
             val (envOverallExit, endPhis) = Env.mergeEnvs ([envExit] @ brks)
             val _ = print ("WHILE MergeEnvOverallExit: " ^ (Env.toString envOverallExit) ^ "\n")
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
         | AddrOf(f) => S.empty
         | Invoke(e, args) => foldl S.union (usedE e) (map usedE args)
         | IntConst _ => S.empty
         | BoolConst _ => S.empty
         | StringConst _ => S.empty
         | CharConst _ => S.empty
         | Alloc _ => S.empty
         | Null => S.empty
         | Result => S.empty
         | Length (e) => usedE e
         | Hastag (tp, e) => usedE e
         | AllocArray (tp, e) => usedE e
         | Cast(tp, e) => usedE e
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
             val _  = print ("Initial Env: " ^ (Env.toString initialEnv) ^ "\n")
             val (s, env, rets, _, _) = ssa (stmt', initialEnv)
             val _  = print ("Final Env: " ^ (Env.toString env) ^ "\n")
             val s' = simplifySeq s
             val s'' = simplifyPhiS s'
          in
             [Function(rtp, name, types, args, reqs', s'', ens')]
          end 
     | analyzeFunc iso _ = []
    
   (* list of vardecls to list of vars *)
   (* this would probably be useful when passing vardecls as arguments to function/basic block tail-calls *)
   fun vardeclsToVars vardecls = 
       map (fn (Ast.VarDecl (ident, _, _, _)) => Ast.Var ident) vardecls

   (* create a new empty basic block *)
   fun createBlock (name, rtp, args, specs) = 
       Ast.Function (name, rtp, args, SOME (Ast.Seq ([], [])), specs, false, NONE)


   fun collectDeclsFromStm l stm =
    case stm of
        Ast.Assign (oper, var, e) => l
      | Ast.Exp e => l	       (* e; *)
      | Ast.Seq (vardecl_list, stm_list) => (foldr (fn (stm, vl) => collectDeclsFromStm vl stm) l stm_list) @ vardecl_list (* { ds es } ; can we assume that ds is empty here after preprocessing? *)
      | Ast.StmDecl decl => decl::l   (* d *)
      | Ast.If (e, s1, s2) => (collectDeclsFromStm l s1) @ (collectDeclsFromStm l s2)	(* if (e) s1 else s2 *)
      | Ast.While (e, loop_invs, s) => extractVarsFromStmt l s            (* while (e) s, loop invs. *)
      | _ => l (* What about Markeds? I think For loops can be safely ignored *)

   (* How to convert to SSA form? *)
   (* The very first step we need to do is to make sure that each function call only have arguments that are constant/variable
      To do so, we need to create a global variable counter (for naming new variables) and traverse the function body recursively:
      whenever we encounter an FunCall, check its arguments to make sure that all arguments are constant/variable. If not, create a
      new variable using Assign and the global counter and append it before the FunCall and replace the argument accordingly *)
   (* After the first transformation, for each function, break it down into basic blocks recursively 
      and add the blocks/functions to a pool (implemented as an array or a map) *)
   (* First, we need to collect some information about the original function
      1. function name/identifier 
      2. return type (would be used as return types for all the subblocks)
      3. arguments (as decls. list)
      4. all local variables defined in the function body (also collected as decls. list) *)
   (* Second, we need to break down its function body recursively.
      we need to create a header/initial block for each original function using the original function name
      Then for each statement:
      - Assign: grab the most recent block (the one with index given by Array.bound) and add the stm to the end of the Seq
      - Exp: same as Assign
      - Seq: it seems that we can assume the first component of Seq is always empty after preprocessing (see line 6 in preprocess.sml);
             thus, we can apply our function on each element of the stm list using List.app
      - StmDecl: same as Assign
      - If (e, strue, sfalse): 2 new blocks need to be created
        - store the index of the current block
        - create and put the strue header block on array then update with strue first: oldArray -> newArray
        - create and put the sfalse header block on array then update with sfalse: newArray -> newArray'
        - retrieve the block before, adding If statement with approrpiate block names
      - While, Break, Continue, For: ignore these cases for now
      - Anno: append the specs to the global spec list for the original function
      - Assert: same as Assign
      - Error: same as Assign
      - Markeds: same as Assign except that we need to extract the stm inside *)
    (* this function should have signature: stm * spec list -> unit *)

    
    (* fun extractBasicBlock (Ast.Function(name, rtp, args, SOME stm, specs, false, ext)) = 
       let val (stm', _) = Preprocess.preprocess iso
                 (Ast.Function(name, rtp, args,
                               SOME (Ast.Markeds (Mark.mark' (stm, ext))),  (* Why do we need to annotate the function body with markeds here? *)
                               specs, false, ext))
            val allArgs = extractVatsFromStmt args stm'
            (* args are all the arguments to the function (of type vardecl list) *)
            (* allArgs are all the arguments to the function plus all local variables defined in the function body (of type vardecl list) *)
            (* counter would be the global counter for creating unique identifier for each basic block *)
            (* stack would be the working stack for the basic blocks of current function (a list of basic blocks) *)
            (* break and continue envs to be added *)
            fun stmToBlock (stm, counter, stack) =
                case stm of
                      Ast.If (e, strue, sfalse)	=> let val BasicBlock (strueIdent, _, _) = stmToBlock (strue, counter, stack)
                                                       val BasicBlock (sfalseIdent, _, _) = stmToBlock (sfalse, counter, stack)
                                                       val ifBlock = createBlock (counter, allArgs, Ast.If (e, Ast.Return (SOME (Ast.FunCall (strueIdent, [])),
                                                                                                               Ast.Return (SOME (Ast.FunCall (sfalseIdent, []))))))
                                                   in   (* if (e) s1 else s2 *)
                                                   end
                    | Ast.While (e, loop_invs, s)            (* while (e) s, loop invs. *)
                    | Ast.Seq (decls, stms) 
                    | _ => stack
       in stmToBlock (stm', allArgs, 0, [BasicBlock(name, args, Ast.Seq([], []))])
       end
     | extractBasicBlock _ = [] *)

   fun analyze iso prog = List.concat (map (analyzeFunc iso) prog)
end


