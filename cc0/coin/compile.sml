signature COMPILE = sig
   
val cStm : Ast.stm -> Mark.ext -> C0Internal.program
val cStms : Ast.stm list -> Mark.ext -> C0Internal.program
 
end

structure Compile:> COMPILE = 
struct

open C0Internal

fun valOf NONE msg = raise Error.Internal msg
  | valOf (SOME e) msg = e

fun cAOp NONE = NONE
  | cAOp (SOME oper) = SOME
   (case oper of Ast.TIMES => Times | Ast.DIVIDEDBY => Div | Ast.MODULO => Mod 
     | Ast.PLUS => Plus | Ast.MINUS => Minus | Ast.SHIFTLEFT => ShiftLeft
     | Ast.SHIFTRIGHT => ShiftRight | Ast.LESS => Lt | Ast.LEQ => Leq
     | Ast.GREATER => Gt | Ast.GEQ => Geq | Ast.EQ => Eq | Ast.NOTEQ => Neq 
     | Ast.AND => BitAnd | Ast.XOR => BitXor | Ast.OR => BitOr 
     | _ => raise Error.Internal "Bad assign operation")

fun mExp pos exp = 
   case exp of
      Ast.Marked mrk => valOf (Mark.ext mrk) "No mark"
    | _ => valOf pos "No position information available"

fun cOpExp (pos : Mark.ext option) opexp = 
   case opexp of 
      (Ast.SUB, [e1, e2]) => Index (cExp pos e1, cExp pos e2)
    | (Ast.LOGNOT, [e1]) => Monop (LogicNot, cExp pos e1)
    | (Ast.COMPLEMENT, [e1]) => Monop (BitNot, cExp pos e1)
    | (Ast.NEGATIVE, [e1]) => Monop (ArithNeg, cExp pos e1)
    | (Ast.DEREF, [e1]) => Ref (cExp pos e1)
    | (Ast.TIMES, [e1, e2]) => Binop (cExp pos e1, Times, cExp pos e2)
    | (Ast.DIVIDEDBY, [e1, e2]) => Binop (cExp pos e1, Div, cExp pos e2)
    | (Ast.MODULO, [e1, e2]) => Binop (cExp pos e1, Mod, cExp pos e2)
    | (Ast.PLUS, [e1, e2]) => Binop (cExp pos e1, Plus, cExp pos e2)
    | (Ast.MINUS, [e1, e2]) => Binop (cExp pos e1, Minus, cExp pos e2)
    | (Ast.SHIFTLEFT, [e1, e2]) => Binop (cExp pos e1, ShiftLeft, cExp pos e2)
    | (Ast.SHIFTRIGHT, [e1, e2]) => Binop (cExp pos e1, ShiftRight, cExp pos e2)
    | (Ast.LESS, [e1, e2]) => Binop (cExp pos e1, Lt, cExp pos e2)
    | (Ast.LEQ, [e1, e2]) => Binop (cExp pos e1, Leq, cExp pos e2)
    | (Ast.GREATER, [e1, e2]) => Binop (cExp pos e1, Gt, cExp pos e2)
    | (Ast.GEQ, [e1, e2]) => Binop (cExp pos e1, Geq, cExp pos e2)
    | (Ast.EQ, [e1, e2]) => Binop (cExp pos e1, Eq, cExp pos e2)
    | (Ast.NOTEQ, [e1, e2]) => Binop (cExp pos e1, Neq, cExp pos e2) 
    | (Ast.AND, [e1, e2]) => Binop (cExp pos e1, BitAnd, cExp pos e2)
    | (Ast.XOR, [e1, e2]) => Binop (cExp pos e1, BitXor, cExp pos e2)
    | (Ast.OR, [e1, e2]) => Binop (cExp pos e1, BitOr, cExp pos e2)
    | (Ast.LOGAND, [e1, e2]) => 
      LogicAnd (cExp pos e1, cExp pos e2)
    | (Ast.LOGOR, [e1, e2]) => 
      LogicOr (cExp pos e1, cExp pos e2)
    | (Ast.COND, [e1, e2, e3]) => 
      Ternary (cExp pos e1, cExp pos e2, cExp pos e3)
    | _ => raise Error.Internal "Bad binary operation"

and cExp (pos : Mark.ext option) exp = 
   case exp of
      Ast.Var x => Var x
    | Ast.IntConst i => Const (Int i)
    | Ast.StringConst s => Const (String s)
    | Ast.CharConst c => Const (Char c)
    | Ast.True => Const (Bool true)
    | Ast.False => Const (Bool false)
    | Ast.Null => Const NullPointer
    | Ast.OpExp opexp => cOpExp pos opexp
    | Ast.Select (exp, field) => Field (cExp pos exp, field)
    | Ast.FunCall (f, es) => 
      Call (f, map (cExp pos) es, valOf pos "No mark for call")
    | Ast.Alloc tp => Alloc tp
    | Ast.AllocArray (tp, exp) => AllocArray (tp, cExp pos exp)
    | Ast.Result => raise Error.Internal "No '\\result' action"
    | Ast.Length exp => Length (cExp pos exp)
    | Ast.Old _ => raise Error.Internal "No '\\old' action"
    | Ast.Marked mrk => cExp (Mark.ext mrk) (Mark.data mrk)

fun cVarDecl (Ast.VarDecl (x, tp, e, pos)) = 
   Declare (tp, x, NONE) ::
   (case e of NONE => [] 
     | SOME e => 
       let val pos = valOf pos "No mark"
       in [ Assign (NONE, Var x, cExp (SOME pos) e, pos) ] end)

fun fake_translate (Assign (NONE, Var x, Call (f, args, pos), _)) = 
       CCall (SOME x, f, args, pos)
  | fake_translate (Exp (Call (f, args, pos), _)) = 
       CCall (NONE, f, args, pos)
  | fake_translate cmd = cmd

fun cStms stms pos =
   let
      val nextlabel = ref 0
      val next = fn () => !nextlabel before nextlabel := 1 + !nextlabel
      fun cStm (d, b, c) (pos : Mark.ext option) stm =
         case stm of 
            Ast.Assign (aop, e1, e2) => 
            [ Assign (cAOp aop, cExp pos e1, cExp pos e2, 
                      valOf pos "No mark for assignment") ]
          | Ast.Exp e1 => 
            [ Exp (cExp pos e1, valOf pos "No mark for exp") ]
          | Ast.StmDecl (Ast.VarDecl (x, tp, NONE, pos)) => 
            [ Declare (tp, x, NONE) ]
          | Ast.StmDecl (Ast.VarDecl (x, tp, SOME e, pos)) =>
            let val pos = valOf pos "No mark" 
            in [ Declare (tp, x, SOME (cExp (SOME pos) e, pos)) ] end
          | Ast.Seq ([], []) => []
          | Ast.Seq (vs, ss) => [ PushScope ] 
            @ List.concat (map cVarDecl vs @ map (cStm (d+1, b, c) pos) ss)
            @ [ PopScope 1 ]
          | Ast.If (e1, stmT, Ast.Seq ([], [])) => 
            let 
               val l = next()
            in 
               [ CondJump (cExp pos e1, mExp pos e1, l) ]
               @ [ PushScope ] @ cStm (d, b, c) pos stmT
               @ [ PopScope 1, Label (l, "end 'if'") ]
            end
          | Ast.If (e1, stmT, stmF) => 
            let 
               val lFalse = next ()
               val lTrue = next ()
               val cT = cStm (d, b, c) pos stmT
               val cF = cStm (d, b, c) pos stmF
            in 
               [ CondJump (cExp pos e1, mExp pos e1, lFalse) ] 
               @ [ PushScope ] @ cT @ [ PopScope 1 ]
               @ [ Jump lTrue, Label (lFalse, "'else' branch") ] 
               @ [ PushScope ] @ cF @ [ PopScope 1 ]
               @ [ Label (lTrue, "end 'if'") ] 
            end
          | Ast.While (e1, invs, stm) => 
            let
               val lStart = next ()
               val lEnd = next ()
               val cmd = cStm (0, SOME lEnd, SOME lStart) pos stm
            in
               [ Label (lStart, "loop") ]
               @ [ CondJump (cExp pos e1, mExp pos e1, lEnd) ] 
               @ cmd @ [ Jump lStart, Label (lEnd, "loop end") ]
            end
          | Ast.For (s1, e2, s3, invs, stm) => 
            raise Error.Internal "For loop encountered"
          | Ast.Continue => 
            if d = 0 then [ Jump (valOf c "No loop to continue") ]
            else [ PopScope d, Jump (valOf c "No loop to continue") ]
          | Ast.Break => 
            if d = 0 then [ Jump (valOf b "No loop to break") ] 
            else [ PopScope d, Jump (valOf b "No loop to break") ]
          | Ast.Return e1 => 
            [ Return (Option.map (fn x => (cExp pos x, mExp pos x)) e1) ]
          | Ast.Assert (e1, (Ast.StringConst s)::_) => 
	    (* fix: allow other strings.  5/16/11 -fp *)
            [ Assert (cExp pos e1, s, mExp pos e1) ]
          | Ast.Assert _ => raise Error.Internal "Unexpected assertion arg"
          | Ast.Anno _ => []
          | Ast.Markeds mrk => 
            (case Mark.ext mrk of 
                NONE => (cStm (d, b, c) pos (Mark.data mrk))
              | SOME pos' => (cStm (d, b, c) (SOME pos') (Mark.data mrk)))

      (* PERF: O(n^2) for no good reason *)
      fun findLabel (i, []) n = raise Error.Internal "Could not find label"
        | findLabel (i, Label (x,_) :: cmds) n = 
          if x = n then i else findLabel (i+1, cmds) n
        | findLabel (i, _ :: cmds) n = findLabel (i+1, cmds) n

      val cmds = List.concat (map (cStm (0, NONE, NONE) (SOME pos)) stms)
      (* val cmds = map fake_translate cmds *)
      val labs = Vector.tabulate (!nextlabel, findLabel (0, cmds))
   in
      (Vector.fromList cmds, labs)
   end

fun cStm x = cStms [ x ] 

end

