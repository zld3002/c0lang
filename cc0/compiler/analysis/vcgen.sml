(* C0 Compiler
 * Verification Condition Generator
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature VCGEN =
sig

  (* Given a function and a debug indicator, generates a list of verification
   * errors for that function. *)
  val generate_vc : AAst.afunc -> bool -> VError.error list

end

structure VCGen :> VCGEN =
struct
  structure C = Conditions

  exception Unimplemented 
  exception CriticalError of VError.error list

  (* Add ternary conditionals to z3 so we can assert about them *)
  (* Use VNote to indicate ifs/whiles and other noteworthy info *)

  (* Assert conditions/loops with phis disjunctions *)

  (* Declare all local variables at start of run in Conditions *)

  (* Make it so lengths are known to be positive (or something) *)
  (* have errors just drop out *)
  (* tests with gcd and binary search errori, continue/break/error *)

  val ZERO = AAst.IntConst(Word32Signed.ZERO)
  val typemap : AAst.tp SymMap.map ref = ref (SymMap.empty)
  val debug = ref false
  val cnt_index = ref 0
  val brk_index = ref 0

  fun opeq e1 e2 = AAst.Op(Ast.EQ, [e1,e2])


  (* Gets all of the expressions that are returned from the function. *)
  fun get_returns stm =
    case stm of
      AAst.Seq(s1,s2) => (get_returns s1) @ (get_returns s2)
    | AAst.Return (SOME e) => [e]
    | AAst.If(e,s1,s2,phis) => (get_returns s1) @ (get_returns s2)
    | AAst.While(cntphis,e,es,s,brkphis) => get_returns s
    | AAst.MarkedS m => get_returns (Mark.data m)
    | _ => []

  (* Replaces each instance of \result with the provided return expression. *)
  fun replace_result retval exp =
    case exp of
      AAst.Op(oper,es) => AAst.Op(oper,List.map (replace_result retval) es)
    | AAst.Call(f,es) => AAst.Call(f,List.map (replace_result retval) es)
    | AAst.Result => retval
    | AAst.Length e => AAst.Length(replace_result retval e)
    | AAst.Old e => AAst.Old(replace_result retval e)
    | AAst.AllocArray(t,e) => AAst.AllocArray(t,replace_result retval e)
    | AAst.Select(e,s) => AAst.Select(replace_result retval e,s)
    | AAst.MarkedE m => replace_result retval (Mark.data m)
    | _ => exp

  (* Converts an expression to be the length of an array as opposed
   * to the array itself. This is for making assertions about array
   * bounds, as we need to keep information about array lengths. *)
  fun array_length make_exp exp =
    case exp of
      AAst.Local(v,i) => make_exp (AAst.Length exp)
    | AAst.Op(oper,es) => 
      (case (oper,es) of
        (Ast.DEREF,[e]) => make_exp (AAst.Length exp)
      | (Ast.COND,[e1,e2,e3]) => 
        (* Improve this for asserts with conds *)
        AAst.Op(Ast.LOGOR,[array_length make_exp e2,array_length make_exp e3])
      | _ => raise Fail "can't assign expression to array type")
    | AAst.AllocArray(t,len) => make_exp len
    | AAst.Select _ => make_exp (AAst.Length exp)
    | AAst.MarkedE m => array_length make_exp (Mark.data m)
    | _ => raise Fail "can't assign expression to array type"

  (* Goes through loop invariant experssions and replaces local variables
   * with the new generation number inidcated by the index into phis. *)
  fun replace_inv phis index switch inv =
    case inv of
      AAst.Local(s,i) =>
        let
          fun replace_phi (AAst.PhiDef(s',i',is),old_i) =
            if switch
              then
                case (Symbol.compare(s,s'),i = List.nth(is,index)) of
                  (EQUAL,true) => i'
                | _ => old_i
              else
                case (Symbol.compare(s,s'),i = i') of
                  (EQUAL,true) => List.nth(is,index)
                | _ => old_i
        in AAst.Local(s,List.foldr replace_phi i phis)
        end
    | AAst.Op(oper,es) => AAst.Op(oper, List.map (replace_inv phis index switch) es)
    | AAst.Call(s,es) => AAst.Call(s,List.map (replace_inv phis index switch) es)
    | AAst.Length e => AAst.Length(replace_inv phis index switch e)
    | AAst.Old e => AAst.Old(replace_inv phis index switch e)
    | AAst.AllocArray(t,e) => AAst.AllocArray(t,replace_inv phis index switch e)
    | AAst.Select(e,s) => AAst.Select(replace_inv phis index switch e,s)
    | AAst.MarkedE m =>
        AAst.MarkedE(Mark.mark' (replace_inv phis index switch (Mark.data m),Mark.ext m))
    | _ => inv

  (* Gets the array in an lvalue if there is one for the purpose of
   * keeping track of array lengths. *)
  fun get_lvarray exp =
    case exp of
      AAst.Local(v,i) =>
        (case SymMap.find(!typemap,v) of
          SOME(Ast.Array _) => SOME exp
        | _ => NONE)
    | AAst.MarkedE m => get_lvarray (Mark.data m)
    | _ => NONE

  (* Returns an expression that is the logical negation of the argument *)
  fun negate_exp exp =
    case exp of
       AAst.Op(Ast.LOGNOT,[e]) => e
     | AAst.Op(Ast.EQ,l) => AAst.Op(Ast.NOTEQ,l)
     | AAst.Op(Ast.NOTEQ,l) => AAst.Op(Ast.EQ,l)
     | AAst.Op(Ast.LESS,l) => AAst.Op(Ast.GEQ,l)
     | AAst.Op(Ast.LEQ,l) => AAst.Op(Ast.GREATER,l)
     | AAst.Op(Ast.GREATER,l) => AAst.Op(Ast.LEQ,l)
     | AAst.Op(Ast.GEQ,l) => AAst.Op(Ast.LESS,l)
     | AAst.Op(Ast.LOGAND,[e1,e2]) => AAst.Op(Ast.LOGOR,[negate_exp e1,negate_exp e2])
     | AAst.Op(Ast.LOGOR,[e1,e2]) => AAst.Op(Ast.LOGAND,[negate_exp e1,negate_exp e2])
     | AAst.MarkedE m => negate_exp (Mark.data m)
     | _ => AAst.Op(Ast.LOGNOT,[exp])

  (* Generates necessary assertions for divions and mods *)
  fun divmod_check ext check e1 e2 =
    (check ext (AAst.Op(Ast.NOTEQ,[e2,ZERO]))) @
    (check ext (AAst.Op(Ast.LOGNOT,[AAst.Op(Ast.LOGAND,
      [opeq e1 (AAst.IntConst(Word32Signed.TMIN)),
       opeq e2 (AAst.IntConst(Word32.fromInt(~1)))])])))

  (* Makes assertions for a given expression *)
  fun process_exp ext check exp =
    case exp of
      AAst.Op(oper,es) => 
          (case (oper,es) of
            (Ast.DEREF,[e]) => check ext (AAst.Op(Ast.NOTEQ,[e,AAst.Null]))
          | (Ast.DIVIDEDBY,[e1,e2]) => divmod_check ext check e1 e2
          | (Ast.MODULO,[e1,e2]) => divmod_check ext check e1 e2
          | (Ast.SUB,[e1,e2]) =>
              (check ext (AAst.Op(Ast.GEQ,[e2,ZERO]))) @ 
              (check ext (array_length (fn l => AAst.Op(Ast.LESS,[e2,l])) e1))
          | _ => [])
    | AAst.AllocArray(t,e) => check ext (AAst.Op(Ast.GEQ,[e,ZERO]))
    | AAst.Select(e,field) => process_exp ext check e
    | AAst.Call(f,es) =>
        List.foldr (fn (e,l) => (process_exp ext check e) @ l) [] es
    | AAst.MarkedE m => process_exp (Mark.ext m) check (Mark.data m)
    | _ => []

  (* Makes assertions for a given statement *)
  fun process_stms ext (funs as (assert,check)) (phi_funs as (cnt_fun,brk_fun)) stms = 
    case stms of
      [] => []
    | stm::cont_stms =>
      (case stm of
        AAst.Nop => process_stms ext funs phi_funs cont_stms
      | AAst.Seq(s1,s2) =>
          process_stms ext funs phi_funs (s1::s2::cont_stms)
      | AAst.Assert e =>
          (process_exp ext check e) @ (check ext e) @
            (process_stms ext funs phi_funs cont_stms)
      | AAst.Error e => raise Unimplemented
      | AAst.Annotation e =>
          (process_exp ext check e) @ (check ext e) @
            (process_stms ext funs phi_funs cont_stms)
      | AAst.Def((v,i),e) =>
          let
              val _ =
                case SymMap.find(!typemap,v) of
                  SOME(Ast.Array _) =>
                    assert (array_length
                      (fn l => opeq (AAst.Length(AAst.Local(v,i))) l) e)
                | _ => ()
              val _ = assert (opeq (AAst.Local(v,i)) e)
          in
            (process_exp ext check e) @ (process_stms ext funs phi_funs cont_stms)
          end
      | AAst.Assign(e1,NONE,e2) =>
          let
            val _ = 
              case get_lvarray e1 of
                SOME arr => 
                  assert (array_length
                    (fn l => opeq (AAst.Length(arr)) l) e2)
              | NONE => () 
            val errs1 = process_exp ext check e1
            val errs2 = process_exp ext check e2
            val _ = assert (opeq e1 e2)
          in
            errs1 @ errs2 @ (process_stms ext funs phi_funs cont_stms)
          end
      | AAst.Assign(e1,SOME oper,e2) =>
          let
            val errs1 = process_exp ext check e1
            val errs2 = process_exp ext check e2
            val _ = assert (opeq e1 (AAst.Op(oper,[e1,e2])))
          in
            errs1 @ errs2 @ (process_stms ext funs phi_funs cont_stms)
          end
      | AAst.Expr e => (process_exp ext check e) @ (process_stms ext funs phi_funs cont_stms)
      | AAst.Return NONE => []
      | AAst.Return (SOME e) =>
          (process_exp ext check e) @ (process_stms ext funs phi_funs cont_stms)
      | AAst.If(e,s1,s2,if_phis) =>
          let
            (* Makes assertions for phi statements *)
            fun assert_phis indices =
              let
                fun assert_phi (AAst.PhiDef(s,i,is)) =
                  assert (List.foldr (fn ((j,e),res) =>
                             AAst.Op(Ast.LOGOR,[res,
                             AAst.Op(Ast.LOGAND,[e,
                                opeq (AAst.Local(s,i))
                                     (AAst.Local(s,List.nth(is,j)))])]))
                           (AAst.BoolConst false)
                           indices)

              in List.map assert_phi if_phis
              end

            val exp_errs = process_exp ext check e

            (* Save the current state for when we do the else case *)
            val _ = C.push()
            (* Assert the condition is true, then check if it is satisfiable
             * (meaning that the then branch could potentially be taken). *)
            val _ = assert e
            val cond_sat = C.check()
            val old_cnt_index = !cnt_index
            val old_brk_index = !brk_index
            (* Generate errors for the then statements given that the conditional is true. *)
            val _ = if cond_sat then print "Entering then case\n" else ()
            val errs = process_stms ext funs phi_funs [s1]
            val thenerrs = if cond_sat then errs else []
            (* Revert to before assertions for then, and resave for doing later statements. *)
            val _ = C.pop()
            val _ = C.push()
            (* Assert the condition is false, then check if it is satisfiable
             * (meaning that the else branch could potentially be taken). *)
            val neg_e = negate_exp e
            val _ = assert neg_e
            val negcond_sat = C.check()
            (* Generate errors for the else statements given that the conditional is false. *)
            val _ = if negcond_sat then print "Entering else case\n" else ()
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
            val _ = print " Exiting if statement\n"
            val resterrs = process_stms ext funs phi_funs cont_stms
          in exp_errs @ thenerrs @ elseerrs @ resterrs
          end
      | AAst.Break =>
          let
            val errs = brk_fun ext (!brk_index)
            val _ = brk_index := !brk_index + 1
          in errs @ (process_stms ext funs phi_funs cont_stms)
          end
      | AAst.Continue =>
          let
            val errs = cnt_fun ext (!cnt_index)
            val _ = cnt_index := !cnt_index + 1
          in errs @ (process_stms ext funs phi_funs cont_stms)
          end
      | AAst.While(cntphis,e,invs,s,brkphis) =>
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
            val cond_sat = C.check()
            val errs = process_stms ext funs
                                    (check_invariants cntphis false,
                                     check_invariants brkphis true) [s]
            (* Now check the case where the loop continues from the end *)
            val errs = errs @ (check_invariants cntphis false ext (!cnt_index))

            val while_errs = if cond_sat then errs else []

            (* Now revert back to outside the loop *)
            val _ = C.pop()

            (* ------------------------------------------------- *)
            (* TODO Assert about constants inside of loop (go through loop again to do this)
             * can just go through loop and assert normally because of SSA? Do we need to 
             * forget what we asserted in there? Is there anything we can learn at all, seeing
             * as we might not even go through the loop? *)
            (* ------------------------------------------------- *)

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
      | AAst.MarkedS m =>
          process_stms (Mark.ext m) funs phi_funs ((Mark.data m)::cont_stms))

  (* The primary function used for making and checking assertions. It produces
   * both warnings and errors (as specified in vcrules.tex). It can also just
   * make regular assertions, for things like assignments where there are no
   * assumptions to check. *)
  fun check_assert assert_fun ext e =
    let
      val _ =
        case (!debug,ext) of
          (true,SOME ext) => print ("Checking at " ^ (Mark.show ext) ^
                 ": " ^ AAst.Print.pp_aexpr e ^ "\n")
        | (true,NONE) => print ("Checking: " ^ AAst.Print.pp_aexpr e ^ "\n")
        | _ => ()

        (* Assert the error case, and if satisfiable, potential values
         * could lead to an error, so give a warning *)
        (* Save the current Z3 stack so we can undo this assumption
         * (since it's explicitly wrong). *)
        val _ = C.push()
        val nege = negate_exp e
        val _ = assert_fun nege
        val sat_error =
          VError.VerificationError(ext,"Error case " ^ 
            (AAst.Print.pp_aexpr nege) ^ " is satisfiable")
        val errs = if C.check() then [sat_error] else []
        val _ = if !debug
          then List.map (fn e => print (VError.pp_error e ^ "\n")) errs
          else []
        (* Now return the stack to as it was so we can make the actual
         * assumption that we wanted to from the beginning. *)
        val _ = C.pop()

        (* Assert the valid case, and if not satisfiable, then code is
         * always wrong, so give an error and stop, because things are bad. *)
        val _ = assert_fun e
        val crit_error =
          VError.VerificationError(ext,"It does not hold that " ^
            (AAst.Print.pp_aexpr e) ^ " when it should")
      in
        (* We stop if we know that something is wrong because everything after
         * that will be wrong, so no useful information can be gained by
         * processing the rest of the function. *)
        if C.check()
          then errs
          else raise CriticalError (errs @ [crit_error])
      end

  (* Generates the vc errors for a given function. *)
  fun generate_vc (f as AAst.Function(_,_,types,args,requires,stm,ensures)) dbg =
    (let
      val assert_fun =
        fn e => C.assert types e
          handle Conditions.Unimplemented s => 
            if !debug
              then print ("Unimplemented assertion for " ^ AAst.Print.pp_aexpr e ^
                          " found in " ^ s ^ "\n")
              else ()
      val _ = typemap := types
      val _ = debug := dbg
      val check = check_assert assert_fun
      fun assert e = (if !debug then print ("Assertion: " ^ AAst.Print.pp_aexpr e ^ "\n")
                                else ();assert_fun e)
      (* Assert what we know from the \requires contracts. *)
      val _ = List.map assert requires
      (* Process the actual function code. *)
      val default_fun = fn x => fn y => []
      val errs = process_stms NONE (assert,check) (default_fun,default_fun) [stm]
      (* Get the list of return values, check that they work in ensures
       * when replacing \result *)
      val retvals = get_returns stm
      val _ = List.map ((List.map (check NONE)) o
                (fn e => List.map (fn r => replace_result r e) retvals)) ensures
    in errs
    end)
      handle CriticalError errs => errs 

end
