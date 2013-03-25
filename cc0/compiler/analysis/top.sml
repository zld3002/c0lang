signature ANALYSISTOP = 
sig
  val purityCheck: Ast.program -> VError.error list
  val staticCheck: Ast.program -> VError.error list
  val verifCheck: Ast.program -> VError.error list
end

structure AnalysisTop :> ANALYSISTOP = 
struct
  fun staticCheck prog =
    let
      fun checkFunc (AAst.Function(rtp, name, types, formals, reqs, s, ens)) =
              NullityAnalysis.checkFunc rtp types reqs s ens
      fun check funcs = List.concat (map checkFunc funcs)
      val funcs = Analysis.analyze false prog
    in
      check funcs
    end
  fun purityCheck prog =
    let
      val funcs = (Analysis.analyze false prog)
                           
      val none = ([], SymMap.empty)
      fun merge [] = none
        | merge [x] = x
        | merge ((e1, m1)::(e2, m2)::rest) =
           let val e = (e1 @ e2, SymMap.unionWith #1 (m1, m2))
           in merge (e::rest) end
           
      fun isPure pf (AAst.Function(rtp, name, types, formals, reqs, s, ens)) =
        isSome (SymMap.find(pf, name))
        
      fun round overallpf funcs_to_check errors_so_far =
        let val fs = List.filter (isPure funcs_to_check) funcs
            val results = map (Purity.purity overallpf) fs
            val (errors, newpure) = merge results
            val errors' = errors @ errors_so_far
        in 
          case SymMap.numItems newpure of
             0 => errors'
           | _ => round (SymMap.unionWith #1 (overallpf, newpure)) newpure errors'
        end
        
      val annotationfuncs = foldr (SymMap.unionWith #1) SymMap.empty
                                  (map (Purity.needspurity) funcs)
    in
      round annotationfuncs annotationfuncs []
    end
  fun verifCheck prog =
    let
      val debug = false
      val print_funcs = false
      val _ = Conditions.StartZ3 ()
      val funcs = Analysis.analyze true prog
      val fun_sums = List.map VCGen.generate_function_summary funcs
      val fun_sum_map = List.foldr SymMap.insert' SymMap.empty fun_sums

      fun checkFunc f =
        (Conditions.reset();VCGen.generate_vc f debug fun_sum_map)
      fun check funcs = List.concat (map checkFunc funcs)

      val _ = if print_funcs
        then print (List.foldr (fn (f,s) => (AAst.Print.pp_afunc f) ^ "\n" ^ s) "" funcs)
        else ()

      val errs = check funcs
      val _ = Conditions.EndZ3 ()
    in
      errs
    end
end
