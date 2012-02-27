(* C0 Compiler
 * SSA Analysis of well typed expressions
 * Jason Koenig <jrkoenig@andrew.cmu.edu>
 *)

signature ANALYSIS = 
sig
   exception UnsupportedConstruct of string
   val analyze: Ast.program -> string
end

signature LOCAL_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol * int
signature SSAENVIRONMENT =
sig
   structure Relabel : LOCAL_MAP
   type symbol = Symbol.symbol
   type relabeling = int Relabel.map
   (* A SSA environment (type env) is a value that maps local symbols to
      integers representing distinct definitions of that local. *)
   type env
   (* This resets the internal next symbol number to zero. *)
   val reset: unit -> unit
   val empty: env
   (* inc takes an environment and a symbol, and returns a new environment which
      is the same except symbol is assigned to a new value. *)
   val inc: env -> symbol -> env
   (* incAll gives a new definition for every variable in the environment.*)
   val incAll: env -> env
   val lookup: env -> symbol -> int option
   val lookup': env -> symbol -> int
   (* Given a list of environments, mergeEnvs will construct a new environment
      in which each symbol has a new, fresh definition if there were differing
      definitions in the inputs, but the same definition if all inputs agree for
      that variable. *)
   val mergeEnvs: env list -> env * (AAst.aphi list)
   (* Given a definition environment, and a list of environments to merge,
      mergeEnvsLoop will construct a new environment along with a set of 
      phi definitions such that everything in the definition environment
      is the phi merge of the inputs, as well as a relabeling of anything defined
      in the definition environment that is only defined in terms of itself and
      one other definition. The relabeling will map the new, redundant definition
      to the one in the input list. *)
   val mergeEnvsLoop: env -> env list -> env * (AAst.aphi list) * relabeling
end

structure SSAEnvironment :> SSAENVIRONMENT =
struct
   structure T = RedBlackMapFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)
	structure SInt = RedBlackSetFn (
	   struct type ord_key = int val compare = Int.compare end)
	
   structure Relabel = RedBlackMapFn (
      struct type ord_key = Symbol.symbol * int
             val compare = (fn ((v,i), (v',i')) => 
                                case Symbol.compare (v,v') of
                                   EQUAL => Int.compare(i,i')
                                 | r => r)
      end)
   type relabeling = int Relabel.map
   
   type symbol = Symbol.symbol
   type env = int T.map
   
   val nexts: int ref = ref 0;
   fun reset () = nexts := 0;
   fun next () = let val i = !nexts
                     val () = nexts := i + 1
                 in i end
                 
   val empty = T.empty
   fun inc env sym = (T.insert (env, sym, next()))
   fun incAll env = T.map (fn i => next()) env
   fun lookup env v = T.find (env, v)
   fun lookup' env v = valOf (T.find (env, v))
   fun mergeEnvs envs =
    let
      fun singleton e = T.map (fn i => SInt.singleton i) e
      fun merge maps = T.unionWith (fn sets => SInt.union sets) maps
      val collected = foldr merge (singleton empty) (map singleton envs)
      val preserved = T.mapPartial
                         (fn s => case SInt.numItems s of
                                     1 => SOME (valOf(SInt.find (fn _ => true) s))
                                   | _ => NONE)
                         collected
      val newDefs = T.mapPartial
                         (fn s => case SInt.numItems s of
                                     1 => NONE
                                   | _ => SOME(next(), SInt.listItems s))
                         collected
      val justNewDefs = T.map (fn (i, _) => i) newDefs
      val env' = T.unionWith (fn (a,b) => b) (preserved, justNewDefs)
      val defs = map (fn (sym, (i, l)) => AAst.PhiDef(sym, i, l))
                     (T.listItemsi newDefs)
    in (env', defs) end
   
   fun mergeEnvsLoop defenv envs =
    let
      fun getRelabeling (v, (i, s)) = 
         let val s' = SInt.difference (s, (SInt.singleton i))
         in case SInt.numItems s' of 
               1 => let val j = valOf(SInt.find (fn _ => true) s')
                    in SOME(i,j) end
             | _ => NONE
         end
      fun getNonTrivialDef (v, (i, s)) = 
         let val s' = SInt.difference (s, (SInt.singleton i))
         in case SInt.numItems s' of 
               1 => NONE
             | _ => SOME(AAst.PhiDef(v, i, SInt.listItems s))
         end        
      fun singleton e = T.map (fn i => SInt.singleton i) e
      fun merge maps = T.unionWith (fn sets => SInt.union sets) maps
      val collected = foldr merge (singleton empty) (map singleton envs)
      val merged = T.intersectWithi (fn (v, i, s) => (i, s))
                                     (defenv, collected)
      val phidefs = T.mapPartiali getNonTrivialDef merged
      val relabelings = foldr (Relabel.insert') (Relabel.empty)
                           (map (fn (v, (i,j)) => ((v,i),j))
                                (T.listItemsi(T.mapPartiali getRelabeling merged)))
      val defenv' = T.mapi (fn (v, i) => case Relabel.find (relabelings, (v,i)) of
                                            SOME j => j
                                          | NONE => i) defenv
    in (defenv', T.listItems phidefs, relabelings)
    end
end

structure Analysis :> ANALYSIS =
struct
   exception UnsupportedConstruct of string
   
   structure Env = SSAEnvironment
   open AAst
   
   (* Label takes an environment and an expression, and produces an aexpr which
      annotates all local variables with their definitions in the environment.*)
   fun label env exp = 
      case exp of
            Ast.Var v => (case Env.lookup env v of
                             NONE => raise Fail "unknown variable, internal bug"
                           | SOME i => Local (v,i))
          | Ast.OpExp(oper, el) => Op(oper, map (label env) el)
          | Ast.FunCall(f, el) => Call(f, map (label env) el)
          | Ast.Marked m => label env (Mark.data m)
          | Ast.IntConst n => IntConst n
          | Ast.True => BoolConst true
          | Ast.False => BoolConst false
          | Ast.Null => Null
          | Ast.Alloc(tp) => Alloc(tp)
          | Ast.AllocArray(tp, e) => AllocArray(tp, label env e)
          | _ => raise UnsupportedConstruct (Ast.Print.pp_exp exp)
   fun relabel rl exp = 
      case exp of 
         Local (v,i) => (case Env.Relabel.find (rl, (v,i)) of 
                           SOME j => Local (v,j)
                         | NONE => Local (v,i))
       | Op (oper, l) => Op(oper, map (relabel rl) l)
       | Call (f, l) => Call(f, map (relabel rl) l)
       | IntConst _ => exp
       | BoolConst _ => exp
       | Default => exp
       | Alloc _ => exp
       | Null => exp
       | AllocArray (tp, e) => AllocArray(tp, relabel rl e)
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
       
   (* If the expression is just a local variable, retrieve it ignoring marking
      information, otherwise return NONE.*)
   fun getLocal exp =
       case exp of 
           Ast.Marked m => getLocal (Mark.data m)
         | Ast.Var v => SOME v
         | _ => NONE     
   fun ssaVarDecl (decls, env, r, b, c) =
      let fun s' (Ast.VarDecl(v, _, SOME ex, _), (s,e, r, b, c)) =
                      let val (sp, ep, _, _, _) = ssa (Ast.Assign(NONE, Ast.Var v, ex), e)
                      in (Seq(s, sp), ep, r, b, c) end
            | s' (Ast.VarDecl(v, _, NONE, _), (s,e, r, b, c)) =
                      let val e' = Env.inc e v in
                      (Seq(s, Def(label e' (Ast.Var v), Default)), e', r, b, c)
                      end
      in foldl s' (Nop,env, r, b, c) decls end
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
     | ssa (Ast.Markeds m, env) = ssa (Mark.data m, env)
     | ssa (Ast.Seq (decls, sl), env) = 
         let fun ssa' (stm, (s, e, r, b, c)) = 
             let val (s', e', r', b', c') = ssa (stm, e) in (Seq(s,s'), e', r@r', b@b', c@c') end
         in foldl ssa' (ssaVarDecl (decls, env, [], [], [])) sl end
     | ssa (Ast.Return NONE, env) = (Return NONE, Env.empty, [env], [], [])
     | ssa (Ast.Return (SOME e), env) =
                        (Return (SOME (label env e)), Env.empty, [env], [], [])
     | ssa (Ast.Break, env) = (Break, Env.empty, [], [env], [])
     | ssa (Ast.Continue, env) = (Continue, Env.empty, [], [], [env])
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
            (relabelStmt relabeling (Seq(While(loopPhis, (label envdef e), map (fn Ast.LoopInvariant (e, _) => label envdef e) specs, stm'),
                 PhiBlock endPhis)),
             envOverallExit, rets, [], [])
         end
     | ssa ((Ast.Exp e), env) = (Expr (label env e), env, [], [], [])
     | ssa ((Ast.Assert (e,_)), env) = (Assert (label env e), env, [], [], [])
     | ssa ((Ast.Anno annos), env) = (foldr (Seq) Nop (map (fn (Ast.Assertion (e, _)) => Annotation (label env e)) annos), env, [], [], [])
     | ssa (stm,e) = raise UnsupportedConstruct (Ast.Print.pp_stm stm)
   
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
       
   fun commas c sl = case sl of
		                     [] => ""
		                  |  x::[] => x
		                  |  x::xs => x ^ c ^ (commas c xs)
	(* DEBUG ONLY: Runs SSA, then constructs a string from the AAst *)	  
   fun analyzeFunc (Ast.Function(name, rtp, args, SOME stmt, specs, false, _)) = 
          (let
             val () = Env.reset();
             val (_, initialEnv, _, _, _) = ssaVarDecl (args, Env.empty, [], [], [])
             val argstring = "args"
             val (s, env, rets, _, _) = ssa (stmt, initialEnv)
             val s' = simplifySeq s
          in (Ast.Print.pp_tp rtp) ^ " " ^ (Symbol.name name)
           ^ "("^ argstring ^")\n{\n" ^ (Print.pp_astmt s') ^"\n}"end
        handle UnsupportedConstruct s => "Unsupported: " ^ s)
     | analyzeFunc _ = ""
   (* DEBUG ONLY: Runs SSA on each function in a program. *)
   fun analyze prog = commas "\n\n" (map analyzeFunc prog)
end
