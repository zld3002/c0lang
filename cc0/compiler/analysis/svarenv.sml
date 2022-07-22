   
signature SVARENVIRONMENT =
sig
   type symbol = Symbol.symbol
   type tp = VAst.tp
   type env
   
   val empty: env

   (* called when encountering a use *)
   val getVersion : env -> symbol -> int
   val getType : env -> symbol -> tp

   (* called when encountering a (first) def *)
   val addVar : env -> symbol -> tp -> env

   (* called when encountering a redef *)
   val updateVar : env -> symbol -> env * int * tp
   
   (* val toString: env -> string *)
end

structure SVAREnvironment :> SVARENVIRONMENT =
struct
   structure T = SymMap

   type symbol = Symbol.symbol
   type tp = VAst.tp
   type env = (int * tp) T.map
                 
   val empty = T.empty
   
   fun getVersion (env: env) (sym: symbol) : int =
      let val (v, _) = T.lookup (env, sym)
      in v end

   fun getType (env: env) (sym: symbol) : tp =
      let val (_, t) = T.lookup (env, sym)
      in t end
   
   fun addVar (env: env) (sym: symbol) (tp: tp) : env =
      T.insert (env, sym, (0, tp))


   (* requires var to be already in the env *)      
   fun updateVar (env: env) (sym: symbol) =
      let val v = getVersion env sym
          val t = getType env sym
          val env' = T.insertWith (fn (old, new) => new) (env, sym, (v + 1, t))
      in (env', v + 1, t) end

  (* fun toString env =
     AAst.Print.commas "," (map (fn (l, i) => Symbol.nameFull l ^ " -> "^ Int.toString i) (T.listItemsi env)) *)
end
