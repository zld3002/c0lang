(* C0 Compiler
 * Verification Condition Generator
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature VCGEN =
sig

  val generate_vc : AAst.afunc -> unit

end

structure VCGen :> VCGEN =
struct
  structure C = Conditions

  exception Unimplemented 

  val ZERO = AAst.IntConst(Word32.fromInt(0))

  (* Tell preprocessing of ssa to do isolation
   * remove conversion, check assigns only at top level *)

  fun convert_array exp = 
    AAst.Length exp

  (*fun convert_length exp = 
    case exp of
      AAst.Op(oper,es) => AAst.Op(oper,List.map convert_length es)
    | AAst.Call(f,es) => AAst.Call(f,List.map convert_length es)
    | AAst.Length e => convert_array e
    | AAst.MarkedE m => convert_length (Mark.data m)	  
    | _ => exp*)

  fun divmod_assert e1 e2 =
    C.assert(AAst.Op(Ast.NOTEQ,[e2,ZERO])) (* add INTMIN /% -1 *)

  fun process_exp exp =
    case exp of
      AAst.Op(oper,es) => 
        ((*List.map process_exp es;*)
          case (oper,es) of
            (Ast.DEREF,[e]) => C.assert (AAst.Op(Ast.NOTEQ,[e,ZERO]))
          | (Ast.DIVIDEDBY,[e1,e2]) => divmod_assert e1 e2
          | (Ast.MODULO,[e1,e2]) => divmod_assert e1 e2
          | (Ast.SUB,[e1,e2]) =>
              (C.assert (AAst.Op(Ast.GEQ,[e2,ZERO]));
          (* consider length in precoditions to be variable, put it in here *)
               C.assert (AAst.Op(Ast.LESS,[e2,convert_array e1])))
          | _ => ())
    | AAst.AllocArray(t,e) => C.assert (AAst.Op(Ast.GEQ,[e,ZERO]))
    | AAst.Select(e,field) => process_exp e
    | AAst.Call(f,es) => (List.map process_exp es;())
    | AAst.MarkedE m => process_exp (Mark.data m)
    | _ => ()

  fun process_stm stm = 
    case stm of
      AAst.Nop => []
    | AAst.Seq(s1,s2) => (process_stm s1) @ (process_stm s2)
    | AAst.Assert e => (process_exp;C.assert e;[])
    | AAst.Annotation e => raise Unimplemented
    | AAst.Def(v,e) =>
    (* Keep track of length if array variable *)
        (process_exp e;C.assert(AAst.Op(Ast.EQ,[AAst.Local v,convert_array e]));[])
    (* assert new info about length of A in assign of array *)
    | AAst.Assign(e1,NONE,e2) =>
        (process_exp e1;process_exp e2;
         C.assert (AAst.Op(Ast.EQ,[e1,e2]));[])
    | AAst.Assign(e1,SOME oper,e2) =>
        (process_exp e1;process_exp e2;
         C.assert (AAst.Op(Ast.EQ,[e1,AAst.Op(oper,[e1,e2])]));[])
    | AAst.Expr e => (process_exp e;[])
    | AAst.Break => raise Unimplemented
    | AAst.Continue => raise Unimplemented
    | AAst.Return NONE => []
    | AAst.Return (SOME e) => (process_exp e;[e])
    | AAst.If(e,s1,s2,phis) => raise Unimplemented
    | AAst.While(cntphis,e,es,s,brkphis) => raise Unimplemented
    | AAst.MarkedS m => process_stm (Mark.data m)

  fun generate_vc (AAst.Function(_,_,_,_,requires,stm,ensures)) = 
    let
      val _ = List.map (C.assert(* o convert_length*)) requires
      val retvals = process_stm stm
      (* Get the list of return values, chack that they work in ensures
       * when replacing \result *)
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
      val _ = List.map ((List.map C.assert) o
                (fn e => List.map (fn f => f e) (List.map replace_result retvals))) ensures
    in if C.check ()
         then ()
         else raise Fail "Conditions did not hold"
    end

end
