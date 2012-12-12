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
  exception CriticalError of VError.error list

  val ZERO = AAst.IntConst(Word32Signed.ZERO)

 (* Add ternary conditionals to z3 so we can assert about them *)

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

  fun get_lvarray typemap exp =
    case exp of
      AAst.Local(v,i) =>
        (case SymMap.find(typemap,v) of
          SOME(Ast.Array _) => SOME exp
        | _ => NONE)
    | AAst.MarkedE m => get_lvarray typemap (Mark.data m)
    | _ => NONE

  fun divmod_assert ext assert e1 e2 =
    (assert ext false (AAst.Op(Ast.NOTEQ,[e2,ZERO]))) @
    (assert ext false (AAst.Op(Ast.LOGNOT,[AAst.Op(Ast.LOGAND,
      [AAst.Op(Ast.EQ,[e1,AAst.IntConst(Word32Signed.TMIN)]),
       AAst.Op(Ast.EQ,[e2,AAst.IntConst(Word32.fromInt(~1))])])])))

  fun process_exp ext assert exp =
    case exp of
      AAst.Op(oper,es) => 
          (case (oper,es) of
            (Ast.DEREF,[e]) => assert ext false (AAst.Op(Ast.NOTEQ,[e,AAst.Null]))
          | (Ast.DIVIDEDBY,[e1,e2]) => divmod_assert ext assert e1 e2
          | (Ast.MODULO,[e1,e2]) => divmod_assert ext assert e1 e2
          | (Ast.SUB,[e1,e2]) =>
              (assert ext false (AAst.Op(Ast.GEQ,[e2,ZERO]))) @ 
              (assert ext false (array_length (fn l => AAst.Op(Ast.LESS,[e2,l])) e1))
          | _ => [])
    | AAst.AllocArray(t,e) => assert ext false (AAst.Op(Ast.GEQ,[e,ZERO]))
    | AAst.Select(e,field) => process_exp ext assert e
    | AAst.Call(f,es) => List.foldr (fn (e,l) => (process_exp ext assert e) @ l) [] es
    | AAst.MarkedE m => process_exp (Mark.ext m) assert (Mark.data m)
    | _ => []

  fun process_stm ext typemap assert stm = 
    case stm of
      AAst.Nop => []
    | AAst.Seq(s1,s2) =>
        (process_stm ext typemap assert s1) @
          (process_stm ext typemap assert s2)
    | AAst.Assert e => (process_exp ext assert e) @ (assert ext false e)
    | AAst.Error e => raise Unimplemented
    | AAst.Annotation e => (process_exp ext assert e) @ (assert ext false e)
    | AAst.Def((v,i),e) =>
        let
          val errs =
            case SymMap.find(typemap,v) of
              SOME(Ast.Array _) =>
                assert ext true (array_length
                  (fn l => AAst.Op(Ast.EQ,[AAst.Length(AAst.Local(v,i)),l])) e)
            | _ => []
        in
          (process_exp ext assert e) @
            (assert ext true (AAst.Op(Ast.EQ,[AAst.Local(v,i),e])))
        end
    | AAst.Assign(e1,NONE,e2) =>
        (case get_lvarray typemap e1 of
          SOME arr => 
            assert ext true (array_length
              (fn l => AAst.Op(Ast.EQ,[AAst.Length(arr),l])) e2)
        | NONE => []) @
          (process_exp ext assert e1) @
          (process_exp ext assert e2) @
          (assert ext true (AAst.Op(Ast.EQ,[e1,e2])))
    | AAst.Assign(e1,SOME oper,e2) =>
        (process_exp ext assert e1) @
          (process_exp ext assert e2) @
          (assert ext true (AAst.Op(Ast.EQ,[e1,AAst.Op(oper,[e1,e2])])))
    | AAst.Expr e => process_exp ext assert e
    | AAst.Break => raise Unimplemented
    | AAst.Continue => raise Unimplemented
    | AAst.Return NONE => []
    | AAst.Return (SOME e) => process_exp ext assert e
    | AAst.If(e,s1,s2,phis) => raise Unimplemented
    | AAst.While(cntphis,e,es,s,brkphis) => raise Unimplemented
    | AAst.MarkedS m => process_stm (Mark.ext m) typemap assert (Mark.data m)

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
      val assert_fun = C.assert types
      val verr = VError.VerificationError
      (* Check asserts, assert what we don't want to be the case, if true (satisfiable),
         then add a warning error. Then assert what we want to be the case, and if that
         fails quit and error because that means that the result always fails. *)
      fun assert ext just_assert e =
        let
          val ext_str =
            case ext of
              NONE => ""
            | SOME e => " at " ^ (Mark.show e)
          val _ =
            if debug
              then print ("Assertion" ^ ext_str ^
                     ": " ^ AAst.Print.pp_aexpr e ^ "\n")
              else ()
          in
            if just_assert
              then (assert_fun e handle Conditions.Unimplemented => ();[])
              else
                let
                  (* Assert the error case, and if satisfiable, give a warning *)
                  val _ = C.push()
                  val nege = negate_exp e
                  val _ = assert_fun nege handle Conditions.Unimplemented => ()
                  val is_sat = C.check()
                  val errs = if is_sat
                        then [verr(ext,"Error case " ^ (AAst.Print.pp_aexpr nege)
                                ^ " is satisfiable")]
                        else []
                  val _ = C.pop()

                  (* Assert the valid case, and if not satisfiable, then code is
                   * always wrong, so give an error and stop, because things are bad. *)
                  val _ = assert_fun e handle Conditions.Unimplemented => ()
                  val is_correct = C.check()
                  val errs = if is_correct
                        then errs
                        else errs @ [verr(ext,"It does not hold that "
                                      ^ (AAst.Print.pp_aexpr e))]
                in
                  if is_correct
                    then errs
                    else raise CriticalError errs
                end
          end
      val _ = List.map (assert NONE true) requires
      val errs = process_stm NONE types assert stm
      (* Get the list of return values, check that they work in ensures
       * when replacing \result *)
      val retvals = get_returns stm
      val _ = List.map ((List.map (assert NONE false)) o
                (fn e => List.map (fn r => replace_result r e) retvals)) ensures
    in errs
    end)
      handle CriticalError errs => errs 

end
