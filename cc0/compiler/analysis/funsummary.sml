(* C0 Compiler
 * Function Summary Generator
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature FUNCTION_SUMMARY =
sig

  type summary = ((AAst.aexpr -> VError.error list) -> AAst.aexpr list ->
                   VError.error list) * (AAst.aexpr list -> AAst.loc -> unit) *
                  ((AAst.tp SymMap.map -> AAst.astmt -> unit) -> 
                    AAst.aexpr list -> AAst.loc -> AAst.astmt) option

  (* Generates summaries of requires/ensures and inlining for all functions *)
  val generate_function_summaries : AAst.afunc list -> summary SymMap.map

end

structure FunctionSummary =
struct

  structure C = Conditions

  open AAst

  type summary = ((AAst.aexpr -> VError.error list) -> AAst.aexpr list ->
                   VError.error list) * (AAst.aexpr list -> AAst.loc -> unit) *
                  ((AAst.tp SymMap.map -> AAst.astmt -> unit) -> 
                    AAst.aexpr list -> AAst.loc -> AAst.astmt) option

  val inline_map : bool SymMap.map ref = ref SymMap.empty
  val max_gen = ref 0
  val alpha_count = ref 0

  (* Returns true if the statement definitely return
   * (but not from inside a loop). *)
  fun definitely_returns stm =
    case stm of
      Seq(s1,s2) => (definitely_returns s1) orelse
                    (definitely_returns s2)
    | Return _ => true
    | If(_,s1,s2,_) => (definitely_returns s1) andalso
                       (definitely_returns s2)
    | MarkedS m => definitely_returns (Mark.data m)
    | _ => false

  (* Returns true if the statement could potentially return
   * (but not from inside a loop). *)
  fun could_return stm =
    case stm of
      Seq(s1,s2) => (could_return s1) orelse
                    (could_return s2)
    | Return _ => true
    | If(_,s1,s2,_) => (could_return s1) orelse
                       (could_return s2)
    | MarkedS m => could_return (Mark.data m)
    | _ => false

  (* Replaces local values with the corresponding term in the map if it
   * exists, otherwise leave them as is. *)
  fun replace_local loc_map e =
    case e of
      Local(s,g) =>
        (case SymMap.find(loc_map,s) of
          NONE => e
        | SOME e => e)
    | Op(oper,es) => Op(oper,List.map (replace_local loc_map) es)
    | Call(s,es) => Call(s,List.map (replace_local loc_map) es)
    | Length e => Length(replace_local loc_map e)
    | Select(e,s) => Select(replace_local loc_map e,s)
    | MarkedE m => replace_local loc_map (Mark.data m)
    | _ => e

  (* Replace \result with the given local. *)
  fun replace_result (l as (sym,gen)) e =
    case e of
      Op(oper,es) => Op(oper,List.map (replace_result l) es)
    | Call(s,es) => Call(s,List.map (replace_result l) es)
    | Result => Local(sym,gen)
    | Length e => Length(replace_result l e)
    | Select(e,s) => Select(replace_result l e,s)
    | MarkedE m => replace_result l (Mark.data m)
    | _ => e

  (* Generates requires/ensures information for a function, for use in verification *)
  fun generate_function_contracts (f as Function(_,sym,types,args,requires,_,ensures)) =
    let
      val old_args = List.map (fn (_,_,(s,_)) => s) args

      fun make_arg_map new_args =
        let
          val arg_list = List.tabulate(List.length args,
                                       fn i => (List.nth(old_args,i),
                                                List.nth(new_args,i)))
        in List.foldr SymMap.insert' SymMap.empty arg_list
        end
      (* Checks that the requires expressions are true given a check function
       * and a list of values to replace the arguments. *)
      fun check_requires check_fun new_args =
        let
          val map = make_arg_map new_args
          val errs = List.map (check_fun o (replace_local map)) requires
        in List.foldr op@ [] errs
        end

      (* Asserts that the ensures expressions are true given a local
       * to replace \result. *)
      fun assert_ensures new_args l =
        let
          val map = make_arg_map new_args
          val _ = List.map (fn e => C.assert types (replace_result l (replace_local map e))
                              handle C.Unimplemented s =>
                                print ("Unimplemented ensures:" ^ s ^ "\n"))
                           ensures
        in ()
        end

    in (check_requires,assert_ensures)
    end

  (* Returns true if the expression can be inlined. It must not 
   * have any recursion (call one of the previously entered functions). *)
  fun can_inline_exp e (funcs as (all_funcs,entered_funcs)) =
    case e of
      Op(_,es) => List.foldr (fn (e,b) =>
                    (can_inline_exp e funcs) andalso b) true es
    | Call(s,es) =>
      let
        val inline =
          (* If we've already checked the function, use that result,
           * otherwise we need to look it up and save that result in
           * case we call the function again. *)
          case SymMap.find(!inline_map,s) of
            SOME b => b
          | NONE =>
             let
              (* If we've already entered the current function, then there
               * is a possible recursive loop, so don't check inlining. *)
               val is_recursive =
                 List.exists (fn f => Symbol.compare(s,f) = EQUAL) entered_funcs
               val b = if is_recursive
                         then false
                         else can_inline_fun funcs s
               val _ = inline_map := SymMap.insert(!inline_map,s,b)
             in b
             end
      in inline andalso
        (List.foldr (fn (e,b) =>
                   (can_inline_exp e funcs) andalso b) true es)
      end
    | Length e => can_inline_exp e funcs
    | Old e => can_inline_exp e funcs
    | AllocArray(_,e) => can_inline_exp e funcs
    | Select(e,_) => can_inline_exp e funcs
    | MarkedE m => can_inline_exp (Mark.data m) funcs
    | _ => true

  (* Returns true if the statement can be inlined. It must not be a loop,
   * or have any recursion. *)
  and can_inline_stm s funcs =
    case s of
      Nop => true
    | Seq(s1,s2) => (can_inline_stm s1 funcs) andalso
                    (can_inline_stm s2 funcs) andalso
                    (* If both paths return, then there is no easy way
                     * to assign the resulting value when inlined.
                     * TODO remove this when inlining for multiple returns
                     * is implemented. *)
                    ((not (could_return s1)) orelse
                     (not (could_return s2)))
    | Assert e => can_inline_exp e funcs
    | Error e => can_inline_exp e funcs
    | Annotation e => can_inline_exp e funcs
    | Def(l,e) => can_inline_exp e funcs
    | Assign(e1,oper,e2) => (can_inline_exp e1 funcs) andalso
                            (can_inline_exp e2 funcs)
    | Expr e => can_inline_exp e funcs
    | Return (SOME e) => can_inline_exp e funcs
    | Return NONE => true
    | If(e,s1,s2,phis) => (can_inline_exp e funcs) andalso
                          (can_inline_stm s1 funcs) andalso
                          (can_inline_stm s2 funcs)
    | MarkedS m => can_inline_stm (Mark.data m) funcs
    | _ => false

  (* Returns true if the function can be inlined. It must not loop, 
   * recur, or return in multiple locations. *)
  and can_inline_fun (all_funcs,entered_funcs) sym =
    let
      val funopt = List.find (fn (Function(_,s,_,_,_,_,_)) => 
                               Symbol.compare(s,sym) = EQUAL) all_funcs
    in
      case funopt of
        NONE => raise Fail "Can't call a non-existant function"
      | SOME(Function(_,_,_,_,_,stm,_)) => can_inline_stm stm (all_funcs,sym::entered_funcs)
    end

  fun alpha_vary_symbol alpha sym =
    Symbol.symbol(Symbol.name sym ^ "-inline" ^ (Int.toString alpha))

  fun alpha_vary_phi alpha (PhiDef(sym,i,is)) =
    PhiDef(alpha_vary_symbol alpha sym,i,is)

  fun alpha_vary_exp alpha e =
    case e of
      Local(sym,gen) => Local(alpha_vary_symbol alpha sym,gen)
    | Op(oper,es) => Op(oper,List.map (alpha_vary_exp alpha) es)
    | Call(sym,es) => Call(alpha_vary_symbol alpha sym,List.map (alpha_vary_exp alpha) es)
    | Length e => Length(alpha_vary_exp alpha e)
    | Old e => Old(alpha_vary_exp alpha e)
    | AllocArray(t,e) => AllocArray(t,alpha_vary_exp alpha e)
    | Select(e,s) => Select(alpha_vary_exp alpha e,s)
    | MarkedE m => MarkedE(Mark.mark' (alpha_vary_exp alpha (Mark.data m),Mark.ext m))
    | _ => e

  fun alpha_vary_stm alpha stm =
    case stm of
      Seq(s1,s2) => Seq(alpha_vary_stm alpha s1,alpha_vary_stm alpha s2)
    | Assert e => Assert(alpha_vary_exp alpha e)
    | Error e => Error(alpha_vary_exp alpha e)
    | Annotation e => Annotation(alpha_vary_exp alpha e)
    | Def((s,g),e) => Def((alpha_vary_symbol alpha s,g),alpha_vary_exp alpha e)
    | Assign(e1,oper,e2) => Assign(alpha_vary_exp alpha e1,oper,alpha_vary_exp alpha e2)
    | Expr e => Expr(alpha_vary_exp alpha e)
    | Return(SOME e) => Return(SOME (alpha_vary_exp alpha e))
    | If(e,s1,s2,phis) => If(alpha_vary_exp alpha e,
                             alpha_vary_stm alpha s1,
                             alpha_vary_stm alpha s2,
                             List.map (alpha_vary_phi alpha) phis)
    | While(cphis,e,invs,s,bphis) => While(List.map (alpha_vary_phi alpha) cphis,
                                           alpha_vary_exp alpha e,
                                           List.map (alpha_vary_exp alpha) invs,
                                           alpha_vary_stm alpha s,
                                           List.map (alpha_vary_phi alpha) bphis)
    | MarkedS m => MarkedS(Mark.mark' (alpha_vary_stm alpha (Mark.data m),Mark.ext m))
    | _ => stm

  fun inline_fun func declare_fun applied_args (result_sym,gen) =
    let
      val Function(_,sym,types,args,_,stm,_) = func
      (* Should modify the statements so that they can be inlined here. *)
      val types = SymMap.foldri (fn (sym,t,m) =>
                                  SymMap.insert(m,alpha_vary_symbol (!alpha_count) sym,t))
                                SymMap.empty
                                types
      val stm = alpha_vary_stm (!alpha_count) stm
      val _ = declare_fun types stm
      val arg_vars = List.map (fn (_,_,(sym,gen)) =>
                       (alpha_vary_symbol (!alpha_count) sym,gen)) args
      val _ = alpha_count := !alpha_count + 1
      fun replace_returns new_gen stm =
        case stm of
          Seq(s1,s2) => Seq(replace_returns new_gen s1,
                            replace_returns new_gen s2)
        | Return (SOME e) => Def((result_sym,new_gen),e)
        | If(e,s1,s2,phis) =>
          (case (could_return s1,could_return s2) of
            (false,false) => If(e,s1,s2,phis)
          | (true,true) => 
            let
              val max = !max_gen
              val s1' = replace_returns max s1
              val s2' = replace_returns (max + 1) s2
              val _ = max_gen := !max_gen + 2
              val new_phi = PhiDef(result_sym,new_gen,[max,max+1])
            in If(e,s1',s2',new_phi::phis)
            end
          | _ => raise Fail "can't inline function that returns in multiple places")
        | MarkedS m => replace_returns new_gen (Mark.data m)
        | _ => stm

      fun make_arg_stms arg_vars applied_args =
        case (arg_vars,applied_args) of
          ([],[]) => replace_returns gen stm
        | (loc::args',aa::aas) =>
          let
            val rest = make_arg_stms args' aas
            val def_arg = Def(loc,aa)
          in Seq(def_arg,rest)
          end
        | _ => raise Fail "unequal number of arguments"

    in make_arg_stms arg_vars applied_args
    end

  fun get_max_gen_exp e =
    case e of
      Local(_,i) => i
    | Op(_,es) => List.foldr Int.max 0 (List.map get_max_gen_exp es)
    | Call(_,es) => List.foldr Int.max 0 (List.map get_max_gen_exp es)
    | Length e => get_max_gen_exp e
    | Old e => get_max_gen_exp e
    | AllocArray(_,e) => get_max_gen_exp e
    | Select(e,_) => get_max_gen_exp e
    | MarkedE m => get_max_gen_exp (Mark.data m)
    | _ => 0

  fun get_max_gen_stm s =
    case s of
      Seq(s1,s2) => 
      Int.max(get_max_gen_stm s1,get_max_gen_stm s2)
    | Assert e => get_max_gen_exp e
    | Error e => get_max_gen_exp e
    | Annotation e => get_max_gen_exp e
    | Def((_,i),e) => Int.max(i,get_max_gen_exp e)
    | Assign(e1,_,e2) =>
      Int.max(get_max_gen_exp e1,get_max_gen_exp e2)
    | Expr e => get_max_gen_exp e
    | Return(SOME e) => get_max_gen_exp e
    | If(e,s1,s2,phis) =>
      Int.max(get_max_gen_exp e,
        Int.max(get_max_gen_stm s1,get_max_gen_stm s2))
    | While(cphis,e,invs,s,bphis) =>
      Int.max(get_max_gen_exp e,get_max_gen_stm s)
    | MarkedS m => get_max_gen_stm (Mark.data m)
    | _ => 0

  fun get_max_generation all_funcs =
    let
      val max_gens = List.map (fn Function(_,_,_,_,_,s,_) => get_max_gen_stm s)
                              all_funcs
    in List.foldr Int.max 0 max_gens
    end

  (* Generates summary information for functions, for use in verification *)
  fun generate_function_summaries all_funcs =
    let
      val _ = inline_map := SymMap.empty

      val _ = max_gen := get_max_generation all_funcs

      fun make_summary s f =
        let
          val (requiresf,ensuresf) = generate_function_contracts f
        in
          if can_inline_fun (all_funcs,[]) s
            then (requiresf,ensuresf,SOME(inline_fun f))
            else (requiresf,ensuresf,NONE)
        end
        
      val fun_sym_pairs = List.map (fn (f as Function(_,sym,_,_,_,_,_)) =>
                                     (sym,f)) all_funcs
      val summaries = List.foldr (fn ((s,f),m) => SymMap.insert(m,s,make_summary s f))
                                 SymMap.empty
                                 fun_sym_pairs

    in summaries
    end

end
