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
  (* Change statements to take in list of errors as argument so 
   * it can use cons and reverse the list at the end? *)

  val ZERO = AAst.IntConst(Word32Signed.ZERO)
  val typemap : AAst.tp SymMap.map ref = ref (SymMap.empty)
  val debug = ref false
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
  fun process_stms ext (funs as (assert,check)) stms = 
    case stms of
      [] => []
    | stm::cont_stms =>
      (case stm of
        AAst.Nop => process_stms ext funs cont_stms
      | AAst.Seq(s1,s2) =>
          process_stms ext funs (s1::s2::cont_stms)
      | AAst.Assert e =>
          (process_exp ext check e) @ (check ext e) @
            (process_stms ext funs cont_stms)
      | AAst.Error e => raise Unimplemented
      | AAst.Annotation e =>
          (process_exp ext check e) @ (check ext e) @
            (process_stms ext funs cont_stms)
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
            (process_exp ext check e) @ (process_stms ext funs cont_stms)
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
            errs1 @ errs2 @ (process_stms ext funs cont_stms)
          end
      | AAst.Assign(e1,SOME oper,e2) =>
          let
            val errs1 = process_exp ext check e1
            val errs2 = process_exp ext check e2
            val _ = assert (opeq e1 (AAst.Op(oper,[e1,e2])))
          in
            errs1 @ errs2 @ (process_stms ext funs cont_stms)
          end
      | AAst.Expr e => (process_exp ext check e) @ (process_stms ext funs cont_stms)
      | AAst.Break => raise Unimplemented
      | AAst.Continue => raise Unimplemented
      | AAst.Return NONE => []
      | AAst.Return (SOME e) =>
          (process_exp ext check e) @ (process_stms ext funs cont_stms)
      | AAst.If(e,s1,s2,phis) =>
          let
            (* Makes assertions for phi statements *)
            fun assert_phis indices =
              let
                fun assert_phi (AAst.PhiDef(s,i,is)) =
                  assert (List.foldr (fn (j,e) =>
                                        AAst.Op(Ast.LOGOR,[e,opeq (AAst.Local(s,i))
                                     (AAst.Local(s,List.nth(is,j)))]))
                                     (AAst.BoolConst false)
                                     indices)

              in List.map assert_phi phis
              end

            (* Save the current state for when we do the else case *)
            val _ = C.push()
            (* Assert the condition is true, then check if it is satisfiable
             * (meaning that the then branch could potentially be taken). *)
            val _ = assert e
            val cond_sat = C.check()
            (* Generate errors for the then statements given that the conditional is true. *)
            val _ = if cond_sat then print "Entering then case\n" else ()
            val thenerrs = if cond_sat then process_stms ext funs [s1] else []
            (* Revert to before assertions for then, and resave for doing later statements. *)
            val _ = C.pop()
            val _ = C.push()
            (* Assert the condition is false, then check if it is satisfiable
             * (meaning that the else branch could potentially be taken). *)
            val _ = assert (negate_exp e)
            val negcond_sat = C.check()
            (* Generate errors for the else statements given that the conditional is false. *)
            val _ = if negcond_sat then print "Entering else case\n" else ()
            val elseerrs = if negcond_sat then process_stms ext funs [s2] else []
            (* Revert to before assertions for else. *)
            val _ = C.pop()
            (* Only process statements of branches that could potentially be taken. *)
            val _ = if cond_sat then process_stms ext funs [s1] else []
            val _ = if negcond_sat then process_stms ext funs [s2] else []
            (* Use phi functions to make assertions about values after the if *)
            val indices = if negcond_sat then [1] else []
            val indices = if cond_sat then 0::indices else indices
            val _ = assert_phis indices
            (* Generate errors for the rest of the statements in the program. *)
            val _ = print " Exiting if statement\n"
            val resterrs = process_stms ext funs cont_stms
          in thenerrs @ elseerrs @ resterrs
          end
      | AAst.While(cntphis,e,es,s,brkphis) => raise Unimplemented
      | AAst.MarkedS m =>
          process_stms (Mark.ext m) funs ((Mark.data m)::cont_stms))

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
          handle Conditions.Unimplemented => 
            if !debug
              then print ("Unimplemented assertion for " ^ AAst.Print.pp_aexpr e ^ "\n")
              else ()
      val _ = typemap := types
      val _ = debug := dbg
      val check = check_assert assert_fun
      fun assert e = (print ("Assertion: " ^ AAst.Print.pp_aexpr e ^ "\n");assert_fun e)
      (* Assert what we know from the \requires contracts. *)
      val _ = List.map (check NONE) requires
      (* Process the actual function code. *)
      val errs = process_stms NONE (assert,check) [stm]
      (* Get the list of return values, check that they work in ensures
       * when replacing \result *)
      val retvals = get_returns stm
      val _ = List.map ((List.map (check NONE)) o
                (fn e => List.map (fn r => replace_result r e) retvals)) ensures
    in errs
    end)
      handle CriticalError errs => errs 

end
