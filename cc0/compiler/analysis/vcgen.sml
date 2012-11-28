(* C0 Compiler
 * Verification Condition Generator
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature VCGEN =
sig

  val generate_vc : AAst.afunc -> bool -> VError.error list

end

structure VCGen :> VCGEN =
struct
  structure C = Conditions

  exception Unimplemented 
  exception CodeError of VError.error list

  val ZERO = AAst.IntConst(Word32Signed.ZERO)

  (* Tell preprocessing of ssa to do isolation (done)
   * remove conversion, check assigns only at top level
   *   <- can then just check top level for things like
   *      array accesses or array assigns*)

  fun convert_array exp = 
    AAst.Length exp

  fun divmod_assert assert e1 e2 =
    (assert(AAst.Op(Ast.NOTEQ,[e2,ZERO]))) @
    (assert(AAst.Op(Ast.LOGNOT,[AAst.Op(Ast.LOGAND,
                [AAst.Op(Ast.EQ,[e1,AAst.IntConst(Word32Signed.TMIN)]),
                 AAst.Op(Ast.EQ,[e2,AAst.IntConst(Word32.fromInt(~1))])])])))

  fun process_exp assert exp =
    case exp of
      AAst.Op(oper,es) => 
        ((*List.map process_exp es;*)
          case (oper,es) of
            (Ast.DEREF,[e]) => assert(AAst.Op(Ast.NOTEQ,[e,ZERO]))
          | (Ast.DIVIDEDBY,[e1,e2]) => divmod_assert assert e1 e2
          | (Ast.MODULO,[e1,e2]) => divmod_assert assert e1 e2
          | (Ast.SUB,[e1,e2]) =>
              (assert (AAst.Op(Ast.GEQ,[e2,ZERO]))) @ 
          (* consider length in precoditions to be variable, put it in here *)
               (assert (AAst.Op(Ast.LESS,[e2,convert_array e1])))
          | _ => [])
    | AAst.AllocArray(t,e) => assert(AAst.Op(Ast.GEQ,[e,ZERO]))
    | AAst.Select(e,field) => process_exp assert e
    | AAst.Call(f,es) => List.foldr (fn (e,l) => (process_exp assert e) @ l) [] es
    | AAst.MarkedE m => process_exp assert (Mark.data m)
    | _ => []

  fun process_stm assert stm = 
    case stm of
      AAst.Nop => []
    | AAst.Seq(s1,s2) => (process_stm assert s1) @ (process_stm assert s2)
    | AAst.Assert e => (process_exp assert e) @ (assert e)
    | AAst.Annotation e => raise Unimplemented
    | AAst.Def(v,e) =>
    (* Keep track of length if array variable *)
        (process_exp assert e) @ (assert(AAst.Op(Ast.EQ,[AAst.Local v,e])))
    (* assert new info about length of A in assign of array *)
    | AAst.Assign(e1,NONE,e2) =>
        (process_exp assert e1) @ (process_exp assert e2) @
          (assert(AAst.Op(Ast.EQ,[e1,e2])))
    | AAst.Assign(e1,SOME oper,e2) =>
        (process_exp assert e1) @ (process_exp assert e2) @
          (assert (AAst.Op(Ast.EQ,[e1,AAst.Op(oper,[e1,e2])])))
    | AAst.Expr e => process_exp assert e
    | AAst.Break => raise Unimplemented
    | AAst.Continue => raise Unimplemented
    | AAst.Return NONE => []
    | AAst.Return (SOME e) => process_exp assert e
    | AAst.If(e,s1,s2,phis) => raise Unimplemented
    | AAst.While(cntphis,e,es,s,brkphis) => raise Unimplemented
    | AAst.MarkedS m => process_stm assert (Mark.data m)

  fun get_returns stm =
    case stm of
      AAst.Seq(s1,s2) => (get_returns s1) @ (get_returns s2)
    | AAst.Return (SOME e) => [e]
    | AAst.If(e,s1,s2,phis) => (get_returns s1) @ (get_returns s2)
    | AAst.While(cntphis,e,es,s,brkphis) => get_returns s
    | AAst.MarkedS m => get_returns (Mark.data m)
    | _ => []

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

  fun generate_vc (AAst.Function(_,_,types,_,requires,stm,ensures)) debug =
    (let
      (* Add call to check in here that if false returns an error for the
       * current location and assertion. *)
      val assert_fun = C.assert types
      val verr = VError.VerificationError
      (* Check asserts, assert what we don't want to be the case, if true (satisfiable),
         then add an warning error. Then assert what we want to be the case, and if that
         fails quit and error because that means that the result always fails. *)
      val assert =
          fn e =>
            let
              val _ = C.push()
              val nege = AAst.Op(Ast.LOGNOT,[e])
              val _ = assert_fun nege
              val is_sat = C.check()
              val errs = if is_sat
                    then [verr(NONE,"Error case " ^ (AAst.Print.pp_aexpr nege)
                            ^ "is satisfiable")]
                    else []
              val _ = C.pop()
              val _ = assert_fun e
              val is_correct = C.check()
              val errs = if is_correct
                    then errs
                    else errs @ [verr(NONE,"It does not hold that "
                                  ^ (AAst.Print.pp_aexpr nege))]
              val errs = if debug
                    (* Have two lists, one for errors and one for debug asserts *)
                    then errs @ [verr(NONE,"Assert: " ^
                          (AAst.Print.pp_aexpr e) ^ "\n")]
                    else errs
            in
              if is_correct
                then errs
                else raise CodeError errs
            end
      val _ = List.map assert requires
      val errs = process_stm assert stm
      (* Get the list of return values, check that they work in ensures
       * when replacing \result *)
      val retvals = get_returns stm
      val _ = List.map ((List.map assert) o
                (fn e => List.map (fn r => replace_result r e) retvals)) ensures
    in errs
    end)
      handle CodeError errs => errs 

end
