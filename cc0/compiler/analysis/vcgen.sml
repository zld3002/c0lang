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

  val ZERO = AAst.IntConst(Word32Signed.ZERO)

  val debug_asserts = ref false

  (* Tell preprocessing of ssa to do isolation (done)
   * remove conversion, check assigns only at top level
   *   <- can then just check top level for things like
   *      array accesses or array assigns*)

  (* Add call to check in here that if false returns an error for the
   * current location and assertion. *)
  fun assert e =
    let val _ = C.assert e
    in if !debug_asserts
        then [VError.VerificationError(NONE,"Assert: " ^ (AAst.Print.pp_aexpr e) ^ "\n")]
        else []
    end

  fun convert_array exp = 
    AAst.Length exp

  fun divmod_assert e1 e2 =
    (assert(AAst.Op(Ast.NOTEQ,[e2,ZERO]))) @
    (assert(AAst.Op(Ast.LOGNOT,[AAst.Op(Ast.LOGAND,
                [AAst.Op(Ast.EQ,[e1,AAst.IntConst(Word32Signed.TMIN)]),
                 AAst.Op(Ast.EQ,[e2,AAst.IntConst(Word32.fromInt(~1))])])])))

  fun process_exp exp =
    case exp of
      AAst.Op(oper,es) => 
        ((*List.map process_exp es;*)
          case (oper,es) of
            (Ast.DEREF,[e]) => assert(AAst.Op(Ast.NOTEQ,[e,ZERO]))
          | (Ast.DIVIDEDBY,[e1,e2]) => divmod_assert e1 e2
          | (Ast.MODULO,[e1,e2]) => divmod_assert e1 e2
          | (Ast.SUB,[e1,e2]) =>
              (assert (AAst.Op(Ast.GEQ,[e2,ZERO]))) @ 
          (* consider length in precoditions to be variable, put it in here *)
               (assert (AAst.Op(Ast.LESS,[e2,convert_array e1])))
          | _ => [])
    | AAst.AllocArray(t,e) => assert(AAst.Op(Ast.GEQ,[e,ZERO]))
    | AAst.Select(e,field) => process_exp e
    | AAst.Call(f,es) => List.foldr (fn (e,l) => (process_exp e) @ l) [] es
    | AAst.MarkedE m => process_exp (Mark.data m)
    | _ => []

  fun process_stm stm = 
    case stm of
      AAst.Nop => []
    | AAst.Seq(s1,s2) => (process_stm s1) @ (process_stm s2)
    | AAst.Assert e => (process_exp e) @ (assert e)
    | AAst.Annotation e => raise Unimplemented
    | AAst.Def(v,e) =>
    (* Keep track of length if array variable *)
        (process_exp e) @ (assert(AAst.Op(Ast.EQ,[AAst.Local v,e])))
    (* assert new info about length of A in assign of array *)
    | AAst.Assign(e1,NONE,e2) =>
        (process_exp e1) @ (process_exp e2) @
          (assert(AAst.Op(Ast.EQ,[e1,e2])))
    | AAst.Assign(e1,SOME oper,e2) =>
        (process_exp e1) @ (process_exp e2) @
          (assert (AAst.Op(Ast.EQ,[e1,AAst.Op(oper,[e1,e2])])))
    | AAst.Expr e => process_exp e
    | AAst.Break => raise Unimplemented
    | AAst.Continue => raise Unimplemented
    | AAst.Return NONE => []
    | AAst.Return (SOME e) => process_exp e
    | AAst.If(e,s1,s2,phis) => raise Unimplemented
    | AAst.While(cntphis,e,es,s,brkphis) => raise Unimplemented
    | AAst.MarkedS m => process_stm (Mark.data m)

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
    let
      val _ = debug_asserts := debug
      val _ = List.map assert requires
      val errs = process_stm stm
      (* Get the list of return values, check that they work in ensures
       * when replacing \result *)
      val retvals = get_returns stm
      val _ = List.map ((List.map assert) o
                (fn e => List.map (fn r => replace_result r e) retvals)) ensures
    in if C.check ()
         then errs
         else errs @ [VError.VerificationError(NONE,"Conditions did not hold")]
    end

end
