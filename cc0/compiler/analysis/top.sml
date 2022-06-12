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
      val foldedProg = Preprocess.fold_stacked_defns prog
      val translatedFunctions =
         List.mapPartial (fn (fdecl as Ast.Function(name, _, _, SOME _, _, false,_))
                                => SOME (name, Trans.trans_func fdecl)
                            | _ => NONE) foldedProg
                                 
      val _ = Modifies.analyze translatedFunctions
 (*      val _ = List.app (fn (n,f) => AUtil.say (Gcl.pp_func (Symbol.name n) f))
                      translatedFunctions *)
    val _ = map (fn (n,f) => NullityAnalysis.checkFunc n f)
                        translatedFunctions (* Saves summaries, round 1 *)
      val _ = map (fn (n,f) => NullityAnalysis.checkFunc n f)
                        translatedFunctions (* Saves summaries, round 2 *)
    in
      List.concat (map (fn (n,f) => NullityAnalysis.checkFunc n f)
                        translatedFunctions)
    end
    
    
  fun purityCheck prog =
    let
      val funcs = (Analysis.analyze false prog)
      val _ = print "==============================\n"
      val _ = print (List.foldr (fn (f,s) => (AAst.Print.pp_afunc f) ^ "\n" ^ s) "" funcs ^ "\n")
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
             0 => (Purity.bind overallpf; errors')
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
      (* Analyze all the functions to convert them into SSA form. It also runs
       * isolation on the functions.
       * NOTE: Isolation will add breaks to loops if the loop condition has an
       * effectual operation in it (like a division or function call). This
       * will make VC not able to properly verify loop invariants for that
       * loop due to the break. *)
      val funcs = Analysis.analyze true prog
      val fun_sum_map = FunctionSummary.generate_function_summaries funcs

      fun checkFunc f =
        (Conditions.reset();VCGen.generate_vc f debug fun_sum_map)
      fun check funcs = List.concat (map checkFunc funcs)

      val _ = if print_funcs
        then print (List.foldr (fn (f,s) => (AAst.Print.pp_afunc f) ^ "\n" ^ s) "" funcs ^ "\n")
        else ()

      val errs = check funcs
      val _ = Conditions.EndZ3 ()
    in
      errs
    end
end
