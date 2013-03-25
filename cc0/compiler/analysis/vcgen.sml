(* C0 Compiler
 * Verification Condition Generator
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature VCGEN =
sig

  type summary = ((AAst.aexpr -> VError.error list) -> AAst.aexpr list -> VError.error list) * (AAst.loc -> unit)

  (* Given a function, generates a summary of its ensures and requires. *)
  val generate_function_summary : AAst.afunc -> (Symbol.symbol * summary)

  (* Given a function and a debug indicator, generates a list of verification
   * errors for that function. *)
  val generate_vc : AAst.afunc -> bool -> summary SymMap.map -> VError.error list

end

structure VCGen :> VCGEN =
struct
  structure C = Conditions

  open AAst

  exception Unimplemented 
  exception CriticalError of VError.error list

  type summary = ((AAst.aexpr -> VError.error list) -> AAst.aexpr list -> VError.error list) * (AAst.loc -> unit)

  (* How do we want to give back the model?
   * Give values of all arguments, and all current values?
   * Return model as pairs of variable and value *)

  (* TODO *)
  (* Add arrays to z3 so we can assert about them *)
  (* Use VNote to indicate ifs/whiles and other noteworthy info *)

  (* Assert conditions/loops with phis disjunctions *)

  (* Test breaks/continues *)
  (* Fix tests for conditions.sml *)
  (* Add/fix pointer checking (implement NULL constant in Z3) *)

  (* tests with gcd and binary search error, continue/break/error *)

  val ZERO = IntConst(Word32Signed.ZERO)
  val typemap : tp SymMap.map ref = ref (SymMap.empty)
  val funmap : summary SymMap.map ref = ref (SymMap.empty)
  val debug = ref false
  val cnt_index = ref 0
  val brk_index = ref 0
  val declaredVars : LocalSet.set ref = ref LocalSet.empty

  fun print_dbg s = if !debug then print s else ()
  fun opeq e1 e2 = Op(Ast.EQ, [e1,e2])

  fun declare_exp decl e =
    case e of
       Local l => decl l
     | Op(oper,es) => (List.map (declare_exp decl) es;())
     | Call(f,es) => (List.map (declare_exp decl) es;())
     | Length e => (declare_exp decl e;
                         C.assert (Op(Ast.GEQ,[Length e,ZERO])))
     | Old e => declare_exp decl e
     | AllocArray(_,e) => declare_exp decl e
     | Select(e,s) => declare_exp decl e
     | MarkedE m => declare_exp decl (Mark.data m)
     | _ => ()

  fun declare_stm decl stm = 
    case stm of
      Seq(s1,s2) => (declare_stm decl s1;
                          declare_stm decl s2)
    | Assert e => declare_exp decl e
    | Error e => declare_exp decl e
    | Annotation e => declare_exp decl e
    | Def(l,e) => (decl l;declare_exp decl e)
    | Assign(e1,oper,e2) => (declare_exp decl e1;
                                  declare_exp decl e2)
    | Expr e => declare_exp decl e
    | Return (SOME e) => declare_exp decl e
    | If(e,s1,s2,_) => (declare_exp decl e;
                             declare_stm decl s1;
                             declare_stm decl s2)
    | While(_,e,lvs,s,_) => (declare_exp decl e;
                                  List.map (declare_exp decl) lvs;
                                  declare_stm decl s)
    | MarkedS m => declare_stm decl (Mark.data m)
    | _ => ()

  (* Gets all of the expressions that are returned from the function. *)
  fun get_returns stm =
    case stm of
      Seq(s1,s2) => (get_returns s1) @ (get_returns s2)
    | Return (SOME e) => [e]
    | If(e,s1,s2,phis) => (get_returns s1) @ (get_returns s2)
    | While(cntphis,e,es,s,brkphis) => get_returns s
    | MarkedS m => get_returns (Mark.data m)
    | _ => []

  (* Replaces each instance of \result with the provided return expression. *)
  fun replace_result retval exp =
    case exp of
      Op(oper,es) => Op(oper,List.map (replace_result retval) es)
    | Call(f,es) => Call(f,List.map (replace_result retval) es)
    | Result => retval
    | Length e => Length(replace_result retval e)
    | Old e => Old(replace_result retval e)
    | AllocArray(t,e) => AllocArray(t,replace_result retval e)
    | Select(e,s) => Select(replace_result retval e,s)
    | MarkedE m => replace_result retval (Mark.data m)
    | _ => exp

  (* Converts an expression to be the length of an array as opposed
   * to the array itself. This is for making assertions about array
   * bounds, as we need to keep information about array lengths. *)
  fun array_length make_exp exp =
    case exp of
      Local(v,i) => make_exp (Length exp)
    | Op(oper,es) => 
      (case (oper,es) of
        (Ast.DEREF,[e]) => make_exp (Length exp)
      | (Ast.COND,[e1,e2,e3]) => 
        (* Improve this for asserts with conds *)
        Op(Ast.LOGOR,[array_length make_exp e2,array_length make_exp e3])
      | _ => raise Fail "can't assign expression to array type")
    | AllocArray(t,len) => make_exp len
    | Select _ => make_exp (Length exp)
    | MarkedE m => array_length make_exp (Mark.data m)
    | _ => raise Fail "can't assign expression to array type"

  (* Goes through loop invariant experssions and replaces local variables
   * with the new generation number inaidcated by the index into phis. *)
  fun replace_inv phis index switch inv =
    case inv of
      Local(s,i) =>
        let
          fun replace_phi (PhiDef(s',i',is),old_i) =
            if switch
              then
                case (Symbol.compare(s,s'),i = List.nth(is,index)) of
                  (EQUAL,true) => i'
                | _ => old_i
              else
                case (Symbol.compare(s,s'),i = i') of
                  (EQUAL,true) => List.nth(is,index)
                | _ => old_i
        in Local(s,List.foldr replace_phi i phis)
        end
    | Op(oper,es) => Op(oper, List.map (replace_inv phis index switch) es)
    | Call(s,es) => Call(s,List.map (replace_inv phis index switch) es)
    | Length e => Length(replace_inv phis index switch e)
    | Old e => Old(replace_inv phis index switch e)
    | AllocArray(t,e) => AllocArray(t,replace_inv phis index switch e)
    | Select(e,s) => Select(replace_inv phis index switch e,s)
    | MarkedE m =>
        MarkedE(Mark.mark' (replace_inv phis index switch (Mark.data m),Mark.ext m))
    | _ => inv

  (* Gets the array in an lvalue if there is one for the purpose of
   * keeping track of array lengths. *)
  fun get_lvarray exp =
    case exp of
      Local(v,i) =>
        (case SymMap.find(!typemap,v) of
          SOME(Ast.Array _) => SOME exp
        | _ => NONE)
    | MarkedE m => get_lvarray (Mark.data m)
    | _ => NONE

  (* Gets the function called in the expression if there is one for
   * checking contracts. *)
  fun get_function exp =
    case exp of
      Call(s,es) =>
        (case SymMap.find(!funmap,s) of
          SOME d => SOME (d,es)
        | _ => NONE)
    | MarkedE m => get_function (Mark.data m)
    | _ => NONE

  (* Returns an expression that is the logical negation of the argument *)
  fun negate_exp exp =
    case exp of
      Op(Ast.LOGNOT,[e]) => e
    | Op(Ast.EQ,l) => Op(Ast.NOTEQ,l)
    | Op(Ast.NOTEQ,l) => Op(Ast.EQ,l)
    | Op(Ast.LESS,l) => Op(Ast.GEQ,l)
    | Op(Ast.LEQ,l) => Op(Ast.GREATER,l)
    | Op(Ast.GREATER,l) => Op(Ast.LEQ,l)
    | Op(Ast.GEQ,l) => Op(Ast.LESS,l)
    | Op(Ast.LOGAND,[e1,e2]) => Op(Ast.LOGOR,[negate_exp e1,negate_exp e2])
    | Op(Ast.LOGOR,[e1,e2]) => Op(Ast.LOGAND,[negate_exp e1,negate_exp e2])
    | MarkedE m => negate_exp (Mark.data m)
    | _ => Op(Ast.LOGNOT,[exp])

  (* Generates necessary assertions for divions and mods *)
  fun divmod_check ext check e1 e2 =
    (check ext (Op(Ast.NOTEQ,[e2,ZERO]))) @
    (check ext (Op(Ast.LOGNOT,[Op(Ast.LOGAND,
      [opeq e1 (IntConst(Word32Signed.TMIN)),
       opeq e2 (IntConst(Word32.fromInt(~1)))])])))

  (* Makes assertions for a given expression *)
  fun process_exp ext check exp =
    case exp of
      Op(oper,es) => 
          (case (oper,es) of
            (Ast.DEREF,[e]) => check ext (Op(Ast.NOTEQ,[e,Null]))
          | (Ast.DIVIDEDBY,[e1,e2]) => divmod_check ext check e1 e2
          | (Ast.MODULO,[e1,e2]) => divmod_check ext check e1 e2
          | (Ast.SUB,[e1,e2]) =>
              (check ext (Op(Ast.GEQ,[e2,ZERO]))) @ 
              (check ext (array_length (fn l => Op(Ast.LESS,[e2,l])) e1))
          | _ => [])
    | AllocArray(t,e) => check ext (Op(Ast.GEQ,[e,ZERO]))
    | Select(e,field) => process_exp ext check e
    | Call(f,es) =>
        List.foldr (fn (e,l) => (process_exp ext check e) @ l) [] es
    | MarkedE m => process_exp (Mark.ext m) check (Mark.data m)
    | _ => []

  (* Makes assertions for a given statement *)
  fun process_stms ext (funs as (assert,check)) (phi_funs as (cnt_fun,brk_fun)) stms = 
    case stms of
      [] => []
    | stm::cont_stms =>
      (case stm of
        Nop => process_stms ext funs phi_funs cont_stms
      | Seq(s1,s2) =>
          process_stms ext funs phi_funs (s1::s2::cont_stms)
      | Assert e =>
          (process_exp ext check e) @ (check ext e) @
            (process_stms ext funs phi_funs cont_stms)
      | Error e => (process_exp ext check e)
      | Annotation e =>
          (process_exp ext check e) @ (check ext e) @
            (process_stms ext funs phi_funs cont_stms)
      | Def((v,i),e) =>
          let
            val _ =
              case SymMap.find(!typemap,v) of
                SOME(Ast.Array _) =>
                  (assert (array_length
                    (fn l => opeq (Length(Local(v,i))) l) e);
                  assert (array_length
                    (fn l => Op(Ast.GEQ,[l,ZERO])) e))
              | _ => ()
            val errs = case get_function e of
                       SOME((rf,ef),es) =>
                         let
                           val errs = rf (check ext) es
                           val _ = ef (v,i)
                         in errs
                         end
                     | NONE => []
            val _ = assert (opeq (Local(v,i)) e)
          in
            (process_exp ext check e) @ errs @ (process_stms ext funs phi_funs cont_stms)
          end
      | Assign(e1,NONE,e2) =>
          let
            val _ = 
              case get_lvarray e1 of
                SOME arr => 
                  (assert (array_length
                    (fn l => opeq (Length(arr)) l) e2);
                  assert (array_length
                    (fn l => Op(Ast.GEQ,[l,ZERO])) e2))
              | NONE => () 
            val errs1 = process_exp ext check e1
            val errs2 = process_exp ext check e2
            val _ = assert (opeq e1 e2)
          in
            errs1 @ errs2 @ (process_stms ext funs phi_funs cont_stms)
          end
      | Assign(e1,SOME oper,e2) =>
          let
            val errs1 = process_exp ext check e1
            val errs2 = process_exp ext check e2
            val _ = assert (opeq e1 (Op(oper,[e1,e2])))
          in
            errs1 @ errs2 @ (process_stms ext funs phi_funs cont_stms)
          end
      | Expr e => (process_exp ext check e) @ (process_stms ext funs phi_funs cont_stms)
      | Return NONE => []
      | Return (SOME e) =>
          (process_exp ext check e) @ (process_stms ext funs phi_funs cont_stms)
      | If(e,s1,s2,if_phis) =>
          let
            (* Makes assertions for phi statements *)
            fun assert_phis indices =
              let
                fun assert_phi (PhiDef(s,i,is)) =
                  assert (List.foldr (fn ((j,e),res) =>
                             Op(Ast.LOGOR,[res,
                             Op(Ast.LOGAND,[e,
                                opeq (Local(s,i))
                                     (Local(s,List.nth(is,j)))])]))
                           (BoolConst false)
                           indices)

              in List.map assert_phi if_phis
              end

            val exp_errs = process_exp ext check e

            (* Save the current state for when we do the else case *)
            val _ = C.push()
            (* Assert the condition is true, then check if it is satisfiable
             * (meaning that the then branch could potentially be taken). *)
            val _ = assert e
            val cond_sat = case C.check() of
                             NONE => false
                           | SOME _ => true
            val old_cnt_index = !cnt_index
            val old_brk_index = !brk_index
            (* Generate errors for the then statements given that the conditional is true. *)
            val _ = if cond_sat then print_dbg "Entering then case\n" else ()
            val errs = process_stms ext funs phi_funs [s1]
            val thenerrs = if cond_sat then errs else []
            (* Revert to before assertions for then, and resave for doing later statements. *)
            val _ = C.pop()
            val _ = C.push()
            (* Assert the condition is false, then check if it is satisfiable
             * (meaning that the else branch could potentially be taken). *)
            val neg_e = negate_exp e
            val _ = assert neg_e
            val negcond_sat = case C.check() of
                                NONE => false
                              | SOME _ => true
            (* Generate errors for the else statements given that the conditional is false. *)
            val _ = if negcond_sat then print_dbg "Entering else case\n" else ()
            val errs = process_stms ext funs phi_funs [s2]
            val elseerrs = if negcond_sat then errs else []
            (* Revert to before assertions for else. *)
            val _ = C.pop()
            val _ = cnt_index := old_cnt_index
            val _ = brk_index := old_brk_index
            (* Reprocess statements for assertion knowledge. *)
            val _ = process_stms ext funs phi_funs [s1]
            val _ = process_stms ext funs phi_funs [s2]
            (* Use phi functions to make assertions about values after the if. *)
            val indices = if negcond_sat then [(1,neg_e)] else []
            val indices = if cond_sat then (0,e)::indices else indices
            val _ = assert_phis indices
            (* Generate errors for the rest of the statements in the program. *)
            val _ = print_dbg " Exiting if statement\n"
            val resterrs = process_stms ext funs phi_funs cont_stms
          in exp_errs @ thenerrs @ elseerrs @ resterrs
          end
      | Break =>
          let
            val errs = brk_fun ext (!brk_index)
            val _ = brk_index := !brk_index + 1
          in errs
          end
      | Continue =>
          let
            val errs = cnt_fun ext (!cnt_index)
            val _ = cnt_index := !cnt_index + 1
          in errs
          end
      | While(cntphis,e,invs,s,brkphis) =>
          let
            (* Check the invariants hold *)
            fun check_invariants phis switch ext index =
              let
                val _ = C.push()
                val invs = 
                  if switch
                    then List.map (replace_inv phis 0 true) invs
                    else invs
                val new_invs = List.map (replace_inv phis index false) invs
                val errs = List.concat(List.map (check ext) new_invs)
                val _ = C.pop()
              in errs
              end

            val exp_errs = process_exp ext check e

            (* Thanks to SSA, everything defined before we enter the loop is a
             * constant inside of and after the loop *)
            val _ = C.push()
            val old_cnt_index = !cnt_index
            val old_brk_index = !brk_index
            val _ = cnt_index := 1
            val _ = brk_index := 1

            (* First make sure that invariants hold before entering the loop *)
            val inv_errs = check_invariants cntphis false ext 0
            (* Assert the condition while inside the loop *)
            val _ = assert e
            (* Assert the loop invariants at the start of the loop *)
            val _ = List.map assert invs
            (* Check if the condition is even satisfiable *)
            val cond_sat = case C.check() of
                             NONE => false
                           | SOME _ => true
            val errs = process_stms ext funs
                                    (check_invariants cntphis false,
                                     check_invariants brkphis true) [s]
            (* Now check the case where the loop continues from the end *)
            val errs = errs @ (check_invariants cntphis false ext (!cnt_index))

            (* Only keep errors if the loop could be entered *)
            val while_errs = if cond_sat then errs else []

            (* Now revert back to outside the loop *)
            val _ = C.pop()

            (* Assert the invariants, since we can assume that they
             * were true upon exiting the loop *)
            val new_invs = List.map (replace_inv brkphis 0 true) invs
            val _ = List.map assert invs
            (* Revert back to old indices of phis *)
            val _ = cnt_index := old_cnt_index
            val _ = brk_index := old_brk_index
            (* Generate errors for the rest of the statements in the program. *)
            val rest_errs = process_stms ext funs phi_funs cont_stms
          in exp_errs @ inv_errs @ while_errs @ rest_errs
          end
      | MarkedS m =>
          process_stms (Mark.ext m) funs phi_funs ((Mark.data m)::cont_stms))

  (* The primary function used for making and checking assertions. It produces
   * both warnings and errors (as specified in vcrules.tex). It can also just
   * make regular assertions, for things like assignments where there are no
   * assumptions to check. *)
  fun check_assert assert_fun ext e =
    let
      val _ =
        case ext of
          SOME ext => print_dbg ("Checking at " ^ (Mark.show ext) ^
                 ": " ^ Print.pp_aexpr e ^ "\n")
        | NONE => print_dbg ("Checking: " ^ Print.pp_aexpr e ^ "\n")

      (* Assert the error case, and if satisfiable, potential values
       * could lead to an error, so give a warning *)
      (* Save the current Z3 stack so we can undo this assumption
       * (since it's explicitly wrong). *)
      val _ = C.push()
      val nege = negate_exp e
      val _ = assert_fun nege
      val sat_error = fn m =>
        VError.VerificationError(ext,"Error case " ^ 
          (Print.pp_aexpr nege) ^ " is satisfiable with model:" ^ m)
      fun print_model m =
        List.foldr (fn (e,s) => "\n" ^ Print.pp_verif_aexpr e ^ s) "" m
      val errs = case C.check() of
                   SOME m => [sat_error (print_model m)]
                 | NONE => []
      val _ = if !debug
        then List.map (fn e => print_dbg (VError.pp_error e ^ "\n")) errs
        else []
      (* Now return the stack to as it was so we can make the actual
       * assumption that we wanted to from the beginning. *)
      val _ = C.pop()

      (* Assert the valid case, and if not satisfiable, then code is
       * always wrong, so give an error and stop, because things are bad. *)
      val _ = assert_fun e
      val crit_error =
        VError.VerificationError(ext,"It does not hold that " ^
          (Print.pp_aexpr e) ^ " when it should")
    in
      (* We stop if we know that something is wrong because everything after
       * that will be wrong, so no useful information can be gained by
       * processing the rest of the function. *)
      case C.check() of
        SOME _ => errs
      | NONE => raise CriticalError (errs @ [crit_error])
    end

  (* Generates summary information for a function, for use in verification *)
  fun generate_function_summary (f as Function(_,sym,_,args,requires,_,ensures)) =
    let
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

      val old_args = List.map (fn (_,_,(s,_)) => s) args

      fun check_requires check_fun new_args =
        let
          val arg_list = List.tabulate(List.length args,
                                       fn i => (List.nth(old_args,i),
                                                List.nth(new_args,i)))
          val map = List.foldr SymMap.insert' SymMap.empty arg_list
          val errs = List.map (check_fun o (replace_local map)) requires
        in List.foldr op@ [] errs
        end

      fun replace_result (l as (sym,gen)) e =
        case e of
          Op(oper,es) => Op(oper,List.map (replace_result l) es)
        | Call(s,es) => Call(s,List.map (replace_result l) es)
        | Result => Local(sym,gen)
        | Length e => Length(replace_result l e)
        | Select(e,s) => Select(replace_result l e,s)
        | MarkedE m => replace_result l (Mark.data m)
        | _ => e

      fun assert_ensures l =
        (List.map (C.assert o (replace_result l)) ensures;())
    in (sym,(check_requires,assert_ensures))
    end

  fun add_note fun_sym errs =
    case errs of
      [] => []
    | _ => (VError.VerificationNote(NONE,"Errors for function " ^ Symbol.name fun_sym))::errs

  (* Generates the vc errors for a given function. *)
  fun generate_vc (f as Function(_,fun_sym,types,args,requires,stm,ensures)) dbg fun_sum_map =
    (let
      val _ = declaredVars := LocalSet.empty
      val declare = C.declare types
      val declare_fun =
        fn l => 
          if LocalSet.member(!declaredVars,l) then ()
            else (declaredVars := LocalSet.add(!declaredVars,l);declare l
              handle C.Unimplemented s => 
                print_dbg ("Unimplemented declaration for " ^ Print.pp_loc l ^
                           " found in " ^ s ^ "\n"))
      val assert_fun =
        fn e => C.assert e
          handle C.Unimplemented s => 
            print_dbg ("Unimplemented assertion for " ^ Print.pp_aexpr e ^
                       " found in " ^ s ^ "\n")
      val _ = typemap := types
      val _ = funmap := fun_sum_map
      val _ = debug := dbg
      val check = check_assert assert_fun
      fun assert e = (print_dbg ("Assertion: " ^ Print.pp_aexpr e ^ "\n");assert_fun e)
      (* Declare the arguments *)
      val _ = List.map (fn (_,_,l) => declare_fun l) args 
      val _ = declare_stm declare_fun stm
      (* Assert what we know from the \requires contracts. *)
      val _ = List.map (declare_exp declare_fun) requires
      val _ = List.map assert requires
      (* Process the actual function code. *)
      val default_fun = fn x => fn y => []
      val errs = process_stms NONE (assert,check) (default_fun,default_fun) [stm]
      (* Get the list of return values, check that they work in ensures
       * when replacing \result *)
      val retvals = get_returns stm
      val _ = List.map ((List.map (check NONE)) o
                (fn e => List.map (fn r => replace_result r e) retvals)) ensures
    in add_note fun_sym errs
    end)
      handle CriticalError errs => add_note fun_sym errs

end
