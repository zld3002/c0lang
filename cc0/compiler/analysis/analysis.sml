signature ANALYSIS = 
sig
   type ssafunc
   val analyze: bool -> Ast.program -> ssafunc list
end

structure Analysis :> ANALYSIS =
struct
   exception ToBeImplemented
   exception Impossible
   (* structure Env = SSAEnvironment *)
   structure SVAREnv = SVAREnvironment
   structure VAst = VAst
   (* val typeContext = ref (Symbol.empty: Ast.tp Symbol.table) *)

  
  structure DA = DynamicArray
  
  type ssafunc = VAst.basicblock DA.array


  fun newSSAFunc size = DA.array (size, VAst.Empty)

  fun addBlock (ssaf : ssafunc, bb : VAst.basicblock) : int =
      let
         val index = DynamicArray.bound ssaf
         val () = DynamicArray.update (ssaf, index + 1, bb)
      in
         index + 1
      end
   
   (* combineStm : VAst.stm * VAst.stm -> VAst.stm *)
   (* combine two statments in order using VAst.Seq*)
   fun combineStm (stm1, stm2) =
     case (stm1, stm2) of 
          (VAst.Seq (sl1), VAst.Seq (sl2)) => VAst.Seq (sl1 @ sl2)
        | (VAst.Seq (sl1), _) => VAst.Seq (sl1 @ [stm2])
        | (_, VAst.Seq (sl2)) => VAst.Seq (stm1 :: sl2)
        | (_, _) => VAst.Seq ([stm1, stm2])
   

   fun addArgsVer decls ver =
      map (fn decl => case decl of 
                          Ast.VarDecl (id, tp, _, ext) => VAst.SVarDecl (id, ver, tp, NONE, ext)) decls
   

   (* add all decls to the env *)
   fun gatherArgs decls env = 
      let fun helper (decl, env) =
             case decl of 
               Ast.VarDecl (id, tp, _, _) => SVAREnv.addVar env id tp
      in foldl helper env decls end

   (* create new ident./symbol for blocks in ssafunc 
      if the original function has name f then all blocks should have name  f/i where i is the index *)
   fun makeBlockName (sym, ssaf) = 
       let val currentIndex = DA.bound ssaf
           val newName = (Symbol.name sym) ^ "/" ^ (Int.toString (currentIndex + 1))
       in Symbol.symbol newName end


   fun makeFunCall (fname, svardecls) = 
       let val elist = map (fn VAst.SVarDecl (vname, i, _, _, _) => VAst.SVar (vname, i)) svardecls
       in VAst.Return (SOME (VAst.FunCall (fname, elist))) end


   fun appendToIndex (ssaf, index, stmNew) = 
       case DA.sub (ssaf, index) of
            VAst.Block (id, rtp, svardecls, stm, specs) =>
               (let
                  val newBlock = VAst.Block (id, rtp, svardecls, combineStm (stm, stmNew), specs)
                in
                  DA.update (ssaf, index, newBlock)
                end)
          | VAst.Empty => raise Impossible
   (* appendToCurrent: ssafunc * VAst.stm -> unit *)
   (* append stmNew to end of current block in ssaf*)
   fun appendToCurrent (ssaf, stmNew) = 
       let val index = DA.bound ssaf
       in appendToIndex (ssaf, index, stmNew) end

   fun updateBlockArgs (ssaf, index, newArgs) = 
       case DA.sub (ssaf, index) of
            VAst.Block (id, rtp, _, stm, specs) =>
               let
                  val newBlock = VAst.Block (id, rtp, newArgs, stm, specs)
               in
                  DA.update (ssaf, index, newBlock)
               end
          | VAst.Empty => raise Impossible
   
   (* old stmtHelper: Ast.stm * svarenv -> VAst.stm * svarenv *)
   (* new stmHelper: Ast.stm * svarenv * ssafunc * symbol * tp * (symbol * svardecl list) * (symbol * svardecl list) -> VAst.stm * svarenv *)
   fun stmtHelper (stmt, env, ssaf, fname, rtp, contInfo, breakInfo) =
       case stmt of 
            Ast.Assign (oper, lv, e) => (case oper of
                                             NONE => let val e' = expHelper (e, env)
                                                     in case lv of
                                                             Ast.Var id => (let val (env', ver, tp) = SVAREnv.updateVar env id
                                                                               val stmt' = VAst.StmDecl (VAst.SVarDecl (id, ver, tp, SOME e', NONE))
                                                                               val () = appendToCurrent (ssaf, stmt')
                                                                            in (stmt', env') end)                             
                                                           | _ => (let val stmt' = VAst.Assign (NONE, expHelper (lv, env), e')
                                                                       val () = appendToCurrent (ssaf, stmt')
                                                                   (* requires var to be already in the env *)    
                                                                   in (stmt', env) end)
                                                     end
                                             (* simplify lv oper= e to lv = lv oper e *)
                                           | SOME oper => stmtHelper (Ast.Assign (NONE, lv, Ast.OpExp (oper, [lv, e])), env, ssaf, fname, rtp, contInfo, breakInfo))
          | Ast.Exp e => let val stmt' = VAst.Exp (expHelper (e, env))
                             val () = appendToCurrent (ssaf, stmt')
                         in (stmt', env) end
          | Ast.Seq (_, slist) => (case slist of
                                       [] => (VAst.Seq ([]), env)
                                     | s::rest => let val (_, env') = stmtHelper (s, env, ssaf, fname, rtp, contInfo, breakInfo)
                                                  in stmtHelper (Ast.Seq ([], rest), env', ssaf, fname, rtp, contInfo, breakInfo) end)
          | Ast.StmDecl decl => let val Ast.VarDecl (id, tp, init, ext) = decl
                                    val init' = case init of 
                                                     NONE => NONE 
                                                   | SOME e => SOME (expHelper (e, env))
                                    val env' = SVAREnv.addVar env id tp
                                    val stmt' = VAst.StmDecl (VAst.SVarDecl (id, 0, tp, init', ext))
                                    val () = appendToCurrent (ssaf, stmt')
                                in (stmt', env') end
          | Ast.If (e, strue, sfalse) => let val prevIndex = DA.bound ssaf
                                             val prevArgs = SVAREnv.toSVarDecls env
                                             val env' = SVAREnv.updateAll env
                                             val args' = SVAREnv.toSVarDecls env'
                                             val (strue', env'') = stmtHelper (strue, env', ssaf, fname, rtp, contInfo, breakInfo)
                                             (* make new block id only after the recursive call since the recursive call may modify ssaf *)
                                             val trueBlockName = makeBlockName (fname, ssaf)
                                             val trueBlock = VAst.Block (trueBlockName, rtp, args', strue', [])
                                             val trueIndex = addBlock (ssaf, trueBlock)
                                             (* Now moving to the false block *)
                                             val env''' = SVAREnv.updateAll env''
                                             val args'' = SVAREnv.toSVarDecls env'''
                                             val (sfalse', env'''') = stmtHelper (sfalse, env''', ssaf, fname, rtp, contInfo, breakInfo)
                                             val falseBlockName = makeBlockName (fname, ssaf)
                                             val falseBlock = VAst.Block (falseBlockName, rtp, args'', sfalse', [])
                                             val falseIndex = addBlock (ssaf, falseBlock)
                                             val stmt' = VAst.If (expHelper (e, env), makeFunCall (trueBlockName, prevArgs), makeFunCall (falseBlockName, prevArgs))
                                             val () = appendToIndex (ssaf, prevIndex, stmt')
                                             val nextEnv = SVAREnv.updateAll env''''
                                             val nextArgs = SVAREnv.updateArgs (nextEnv, prevArgs)
                                             val nextName = makeBlockName (fname, ssaf)
                                             val nextBlock = VAst.Block (nextName, rtp, nextArgs, VAst.Seq ([]), [])
                                             val _ = addBlock (ssaf, nextBlock)
                                             val () = appendToIndex (ssaf, trueIndex, makeFunCall (nextName, SVAREnv.updateArgs (env'', prevArgs)))
                                             val () = appendToIndex (ssaf, falseIndex, makeFunCall (nextName, SVAREnv.updateArgs (env'''', prevArgs)))
                                         in (stmt', nextEnv) end
          | Ast.While (cond, loopInvs, loopBody) => let val prevIndex = DA.bound ssaf
                                                        val prevArgs = SVAREnv.toSVarDecls env
                                                        val env' = SVAREnv.updateAll env
                                                        val args' = SVAREnv.toSVarDecls env'
                                                        (* We need loop and next placeholder be created and placed first for conInfo'/breakInfo' in the
                                                           recursive call *)
                                                        val loopName = makeBlockName (fname, ssaf)
                                                        val loopBlock = VAst.Block (loopName, rtp, args', VAst.Seq([]), map (fn inv => specHelper (inv, env')) loopInvs)
                                                        val loopIndex = addBlock (ssaf, loopBlock)
                                                        val nextName = makeBlockName (fname, ssaf)
                                                        val nextBlock = VAst.Block (nextName, rtp, [], VAst.Seq([]), [])
                                                        val nextIndex = addBlock (ssaf, nextBlock)
                                                        
                                                        val stmt' = makeFunCall (loopName, prevArgs)
                                                        val contInfo' = (loopName, prevArgs)
                                                        val breakInfo' = (nextName, prevArgs)
                                                        val (loopBody', env'') = stmtHelper (loopBody, env', ssaf, fname, rtp, contInfo', breakInfo')
                                                        val cond' = expHelper (cond, env')
                                                        val contLoop = makeFunCall (loopName, SVAREnv.updateArgs (env'', prevArgs))
                                                        val exitLoop = makeFunCall (nextName, SVAREnv.updateArgs (env', prevArgs))
                                                        val body = VAst.If (cond', VAst.Seq ([loopBody', contLoop]), exitLoop)                                       
                                                        val () = appendToIndex (ssaf, loopIndex, body)
                                                        val nextEnv = SVAREnv.updateAll env''
                                                        val nextArgs = SVAREnv.updateArgs (nextEnv, prevArgs)
                                                        val () = updateBlockArgs (ssaf, nextIndex, nextArgs)
                                             in (stmt', nextEnv) end
          | Ast.Continue => let val (loopName, args) = contInfo
                                val stmt' = makeFunCall (loopName, SVAREnv.updateArgs (env, args))
                            in (stmt', env) end
          | Ast.Break => let val (nextName, args) = breakInfo
                            val stmt' = makeFunCall (nextName, SVAREnv.updateArgs (env, args))
                        in (stmt', env) end
          | Ast.Return e => (case e of
                                 NONE => let val stmt' = VAst.Return (NONE)
                                             val () = appendToCurrent (ssaf, stmt')
                                         in (stmt', env) end
                               | SOME e => let val stmt' = VAst.Return (SOME (expHelper (e, env)))
                                               val () = appendToCurrent (ssaf, stmt')
                                           in (stmt', env) end)
          | Ast.Assert (e, msgs) => let val stmt' = VAst.Assert (expHelper (e, env), map (fn msg => expHelper (msg, env)) msgs)
                                        val () = appendToCurrent (ssaf, stmt')
                                    in (stmt', env) end
          | Ast.Error e => let val stmt' = VAst.Error (expHelper (e, env))
                               val () = appendToCurrent (ssaf, stmt')
                           in (stmt', env) end
          | Ast.Anno specs => let val stmt' = VAst.Anno (map (fn spec => specHelper (spec, env)) specs)
                                  val () = appendToCurrent (ssaf, stmt')
                              in (stmt', env) end 
          | Ast.Markeds _ => raise ToBeImplemented

   (* expHelper: Ast.exp * svarenv -> VAst.exp *)
   (* exp only involves use (not def) of a variable? *)
   (* does that mean the svarenv must be the same as we passed in? *)
   (* i.e. no need to output env *)
   and expHelper (e, env) = 
       case e of
            Ast.Var id => VAst.SVar (id, SVAREnv.getVersion env id)
          | Ast.IntConst i => VAst.IntConst i
          | Ast.StringConst s => VAst.StringConst s
          | Ast.CharConst c => VAst.CharConst c
          | Ast.True => VAst.True
          | Ast.False => VAst.False
          | Ast.Null => VAst.Null
          | Ast.OpExp (oper, elist) => let val elist' = map (fn e => expHelper (e, env)) elist
                                       in VAst.OpExp (oper, elist')
                                       end
          | Ast.Select (e, id) => VAst.Select (expHelper (e, env), id)
          | Ast.FunCall (id, elist) => let val elist' = map (fn e => expHelper (e, env)) elist
                                       in VAst.FunCall (id, elist')
                                       end
         | Ast.AddrOf id => VAst.AddrOf id
         | Ast.Invoke (e, elist) => let val elist' = map (fn e => expHelper (e, env)) elist
                                    in VAst.Invoke (expHelper (e, env), elist')
                                    end
         | Ast.Alloc tp => VAst.Alloc tp
         | Ast.AllocArray (tp, e) => VAst.AllocArray (tp, expHelper (e, env))
         | Ast.Cast (tp, e) => VAst.Cast (tp, expHelper (e, env))
         | Ast.Result => VAst.Result
         | Ast.Length e => VAst.Length (expHelper (e, env))
         | Ast.Hastag (tp, e) => VAst.Hastag (tp, expHelper (e, env))
         (* | Ast.Marked x => VAst.Marked x *)
   and specHelper (spec, env) =
       case spec of
           Ast.Requires (e, x) => VAst.Requires (expHelper (e, env), x)
         | Ast.Ensures (e, x) => VAst.Ensures (expHelper (e, env), x)
         | Ast.LoopInvariant (e, x) => VAst.LoopInvariant (expHelper (e, env), x)
         | Ast.Assertion (e, x) => VAst.Assertion (expHelper (e, env), x)


   fun analyzeFuncNew (Ast.Function(name, rtp, args, SOME stmt, specs, false, ext)) = 
          let
             val (stmt', types) = Preprocess.preprocess true
                 (Ast.Function(name, rtp, args,
                               SOME (Ast.Markeds (Mark.mark' (stmt, ext))),
                               specs, false, ext))
             val args' = addArgsVer args 0
             (* Here we use args rather than args' since the version init. would be handled by gatherArgs *)
             val env = gatherArgs args (SVAREnv.empty)
             val ssaf = newSSAFunc 10
             val leadBlock = VAst.Block (name, rtp, args', VAst.Seq [], map (fn spec => specHelper (spec, env)) specs)
             val _ = addBlock (ssaf, leadBlock)
             (* Note that we are at the top level; therefore there is no cont/break info*)
             val (stmt'', env') = stmtHelper (stmt', env, ssaf, name, rtp, (Symbol.symbol "#NO_CONT", []), (Symbol.symbol "#NO_BREAK", []))
          in
             ssaf
          end 
     | analyzeFuncNew _ = raise Impossible

   fun analyze iso prog = map analyzeFuncNew prog
end


