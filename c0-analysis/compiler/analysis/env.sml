signature LOCAL_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol * int
signature SYM_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol

structure LocalMap :> LOCAL_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol * int
             val compare = (fn ((v,i), (v',i')) => 
                                case Symbol.compare (v,v') of
                                   EQUAL => Int.compare(i,i')
                                 | r => r)
      end)
structure SymMap :> SYM_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)
   
signature SSAENVIRONMENT =
sig
   type symbol = Symbol.symbol
   type relabeling = int LocalMap.map
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
   structure T = SymMap
	structure SInt = RedBlackSetFn (
	   struct type ord_key = int val compare = Int.compare end)
	
   type relabeling = int LocalMap.map
   
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
      fun getNonTrivialDef (v, (i, s, l)) = 
         let val s' = SInt.difference (s, (SInt.singleton i))
         in case SInt.numItems s' of 
               1 => NONE
             | _ => SOME(AAst.PhiDef(v, i, l))
         end        
      fun singleton e = T.map (fn i => SInt.singleton i) e
      fun singleton' e = T.map (fn i => [i]) e
      fun merge maps = T.unionWith (fn sets => SInt.union sets) maps
      fun merge' maps = T.unionWith (op@) maps
      val collected = foldr merge (singleton empty) (map singleton envs)
      val collected' = foldr merge' (singleton' empty) (map singleton' envs)
      val merged = T.intersectWith (fn (i, s) => (i, s))
                                     (defenv, collected)
      val merged' = T.intersectWith (fn ((i, s), l) => (i, s, l))
                                     (merged, collected')
      val phidefs = T.mapPartiali getNonTrivialDef merged'
      val relabelings = foldr (LocalMap.insert') (LocalMap.empty)
                           (map (fn (v, (i,j)) => ((v,i),j))
                                (T.listItemsi(T.mapPartiali getRelabeling merged)))
      val defenv' = T.mapi (fn (v, i) => case LocalMap.find (relabelings, (v,i)) of
                                            SOME j => j
                                          | NONE => i) defenv
    in (defenv', T.listItems phidefs, relabelings)
    end
end
