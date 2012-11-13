signature ANALYSISTOP = 
sig
  val purityCheck: Ast.program -> VError.error list
  val staticCheck: Ast.program -> VError.error list
end

structure AnalysisTop :> ANALYSISTOP = 
struct
  fun staticCheck prog =
    let
      fun checkFunc (AAst.Function(rtp, name, types, formals, reqs, s, ens)) =
              NullityAnalysis.checkFunc rtp types reqs s ens
      fun check funcs = List.concat (map checkFunc funcs)
      val funcs = Analysis.analyze true prog
    in
      check funcs
    end
  fun purityCheck prog =
    let
      val funcs = (Analysis.analyze false prog)
      val purefuncs = (foldr SymSet.union SymSet.empty
                           (map Purity.needspurity funcs))
      fun isPure (AAst.Function(rtp, name, types, formals, reqs, s, ens)) =
        SymSet.member(purefuncs, name)
    in
      List.concat (map (Purity.purity purefuncs) (List.filter isPure funcs))
    end
end
