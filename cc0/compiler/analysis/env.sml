   
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

   val toString: env -> string
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
   
   fun liftMapList maps =
     let val allDomain = foldl (T.unionWith #1) T.empty maps
     in T.mapi (fn (k, _) => map (fn m => T.find(m,k)) maps) allDomain end
   local 
     fun atMostOne [] = NONE
       | atMostOne (x::xs) = (case List.all (fn y => x = y) xs of
                                true => SOME x | false => NONE)
   in
     fun uniqueValue x = atMostOne (List.mapPartial (fn i=>i) x)
     fun uniqueValueWithout v lst = 
      (case atMostOne (List.mapPartial (fn (SOME l) => if l = v then NONE else (SOME l) 
                                           | NONE => NONE) lst) of 
          SOME u => SOME u
        | NONE => uniqueValue lst)
   end
     
   fun mergeEnvs envs =
    let
      val info = T.mapi 
        (fn (sym, locals) =>
            case uniqueValue locals of 
              SOME l => (NONE, SOME l)
            | NONE => let val n = next() in
                      (SOME(AAst.PhiDef(sym, n, map (fn l => getOpt(l, n)) locals)),
                       SOME n)
                      end) (liftMapList envs)
      val env' = T.mapPartial (fn (phi, def) => def) info
      val phis = T.mapPartial (fn (phi, def) => phi) info
      
    in (env', T.listItems phis) end
   
   fun mergeEnvsLoop defenv envs =
    let
      val info = T.mapPartiali 
        (fn (sym, (SOME d)::locals) =>
          SOME (case (uniqueValueWithout d locals) of 
                   SOME l => (NONE, SOME l, SOME(d,l))
                 | NONE => (SOME(AAst.PhiDef(sym, d, map (fn l => getOpt(l, d)) locals)),
                               SOME d, NONE))
          | (sym, NONE :: locals) => NONE                        
        ) (liftMapList (defenv::envs))
            
      val env' = T.mapPartial (fn (phi, def, relabel) => def) info
      val phis = T.mapPartial (fn (phi, def, relabel) => phi) info
      val relabeling = T.mapPartial (fn (phi, def, relabel) => relabel) info
      val relabeling' = foldr (LocalMap.insert') (LocalMap.empty)
                           (map (fn (v, (i,j)) => ((v,i),j)) (T.listItemsi relabeling))
    in (env', T.listItems phis, relabeling')
    end
  fun toString env =
     AAst.Print.commas "," (map (fn (l, i) => Symbol.nameFull l ^ " -> "^ Int.toString i) (T.listItemsi env))
end
