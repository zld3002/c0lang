(* C0 Compiler
 * Constraint store for VCGen
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature CONDITIONS =
sig

  val assert : AAst.aexpr -> unit

  (* Should really return a datatype containing more information, but just use
   * a boolean for now. *)
  val check : unit -> bool

  (* Stores the current set of assertions for later use *)
  val push : unit -> unit

  (* Updates the assertions to be the most recently stored  *)
  val pop : unit -> unit

  val StartZ3 : unit -> unit

  val EndZ3 : unit -> unit

  val z3Started : unit -> bool

end

structure Conditions :> CONDITIONS =
struct

  val z3proc : ((TextIO.instream * TextIO.outstream) *
		(TextIO.instream, TextIO.outstream) Unix.proc) option ref
    = ref NONE
  val z3StackSize : int ref = ref 0

  exception Z3NotStarted
  exception Z3InvalidStack
  exception Unimplemented

  fun z3Started () : bool =
      case (! z3proc) of
	  NONE => false
	| _ => true

  fun StartZ3 () =
      if (z3Started()) then ()
      else
	  let
	      val p = Unix.execute("../../externals/z3/z3", ["-smt2", "-in"])
	  in
	      (z3proc := SOME (
	       (Unix.textInstreamOf(p), Unix.textOutstreamOf(p)),
	       p));
	      ()
	  end

  fun EndZ3 () =
      if (z3Started()) then
	  let
	      val SOME ((a, b), p) = ! z3proc
	  in
	      Unix.kill(p, Posix.Signal.kill);
	      Unix.reap(p);
	      (z3proc := NONE);
	      ()
	  end
      else
	  raise Z3NotStarted
  fun printToZ3 (str : string) =
      let
	  val SOME ((istr, ostr), p) = !z3proc
      in
	  (*print(">> " ^ str);*)
	  TextIO.output(ostr, str);
	  TextIO.flushOut(ostr);
	  ()
      end
      
  fun readFromZ3() =
      let
	  val SOME ((istr, ostr), p) = !z3proc
	  val SOME str = TextIO.inputLine(istr)
      in
	  if String.isPrefix("(error")(str) then
	      (
	       (*print("<< " ^ str);*)
	      readFromZ3()
	      )
	  else
	      (
	       (*print("<< " ^ str);*)
	       str
	      )
      end

  fun assert e =
	  if (z3Started()) then
      let
	  fun getLocalList(e : AAst.aexpr list) : AAst.aexpr list =
	      case e of
		  [] => []
		| x::xs => (
		  case x of
		      AAst.Local((sym, gen)) => [x]
		    | AAst.Op(oper, exprlist) => getLocalList(exprlist)
		    | AAst.Call(sym, exprlist) => getLocalList(exprlist)
		    | AAst.IntConst(word) => []
		    | AAst.BoolConst(bool) => []
		    | AAst.StringConst(str) => []
		    | AAst.CharConst(ch) => []
		    | AAst.Alloc(tp) => []
		    | AAst.Null => []
		    | AAst.Result => []
		    | AAst.Length(expr) => getLocalList([expr])
		    | AAst.Old(expr) => getLocalList([expr])
		    | AAst.AllocArray(tp,expr) => getLocalList([expr])
		    | AAst.Select(expr,sym) => getLocalList([expr])
		    | AAst.MarkedE(mk) => []
		  )@getLocalList(xs)

	  fun localName(e : AAst.aexpr) =
	      let
		  val AAst.Local((sym, gen)) = e;
	      in
		  (Symbol.name(sym)) ^ "_" ^ (Int.toString(gen))
	      end

	  fun assert_expr(e : AAst.aexpr) =
	      case e of
		  AAst.Local((sym, gen)) => localName(e)
		| AAst.Op(oper, exprlist) => (
		  case oper of
		      Ast.SUB => raise Unimplemented
		    | Ast.LOGNOT => (
		      let
			  val [x] = exprlist
		      in
			  "(not " ^ (assert_expr(x)) ^ ")"
		      end)
		    | Ast.COMPLEMENT => (
		      let
			  val [x] = exprlist
		      in
			  "(bvxnor " ^ (assert_expr(x)) ^ " (_ bv0 32))"
		      end)
		    | Ast.NEGATIVE => (
		      let
			  val [x] = exprlist
		      in
			  "(bvneg " ^ (assert_expr(x)) ^ ")"
		      end
		      )
		    | Ast.DEREF => raise Unimplemented
		    | Ast.TIMES => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvmul " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end
		      )
		    | Ast.DIVIDEDBY => raise Unimplemented
		    | Ast.MODULO => raise Unimplemented
		    | Ast.PLUS => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvadd " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.MINUS => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvsub " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.SHIFTLEFT => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvshl " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.SHIFTRIGHT => ( (*DEFAULT TO ARITHMETIC SHIFT RIGHT*)
		      let
			  val [x,y] = exprlist
		      in
			  "(bvashr " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.LESS => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvslt " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.LEQ => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvsle " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.GREATER => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvsgt " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.GEQ => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvsge " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.EQ => (
		      let
			  val [x,y] = exprlist
		      in
			  "(= " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.NOTEQ => (
		      let
			  val [x,y] = exprlist
		      in
			  "(not (= " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ "))"
		      end)
		    | Ast.AND => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvand " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.XOR => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvxnor (bvxnor " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ") (_ bv0 32))"
		      end)
		    | Ast.OR => (
		      let
			  val [x,y] = exprlist
		      in
			  "(bvor " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.LOGAND => (
		      let
			  val [x,y] = exprlist
		      in
			  "(and " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.LOGOR => (
		      let
			  val [x,y] = exprlist
		      in
			  "(or " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
		      end)
		    | Ast.COND => raise Unimplemented
		  )
		| AAst.Call(sym, exprlist) => raise Unimplemented
		| AAst.IntConst(word) => (
		  "(_ bv" ^ Word32.fmt(StringCvt.DEC)(word) ^ " 32)")
		| AAst.BoolConst(bool) => (Bool.toString bool)
		| AAst.StringConst(str) => raise Unimplemented
		| AAst.CharConst(ch) => raise Unimplemented
		| AAst.Alloc(tp) => raise Unimplemented
		| AAst.Null => ("(_ bv0 32)")
		| AAst.Result => raise Unimplemented
		| AAst.Length(expr) => raise Unimplemented
		| AAst.Old(expr) => raise Unimplemented
		| AAst.AllocArray(tp,expr) => raise Unimplemented
		| AAst.Select(expr,sym) => raise Unimplemented
		| AAst.MarkedE(mk) => raise Unimplemented

	  val local_list = getLocalList([e])
	  fun printList(ls) =
	      case ls of
		  [] => ()
		| x::xs =>
		  (print(localName(x) ^ ",");printList(xs);())
	  fun declareList(ls) =
	      case ls of
		  [] => ()
		| x::xs => (printToZ3("(declare-const " ^ (localName(x)) ^ " (_ BitVec 32))\n");())

	  val raw_expr = assert_expr(e)
      in
	  (*(case local_list of
	       [] => ()
	     | _ => (
	       print("Local list:[");printList(local_list);print("]\n")));
	  print("raw_expr: " ^ (raw_expr) ^ "\n");*)
	  declareList(local_list);
	  printToZ3("(assert " ^ raw_expr ^ ")\n");
	  ()
      end
	  else
	      raise Z3NotStarted
      
  fun check () =
      if (z3Started()) then
	  let
	      val SOME ((istr, ostr), p) = !z3proc
	      val _ = printToZ3("(check-sat)\n")
	      val str = readFromZ3()
	  in	  
	      case String.compare(str, "sat\n") of
		  EQUAL => true | _ => false
	  end
      else
	  raise Z3NotStarted

  fun push () = 
      if (z3Started()) then
	  let
	      val _ = printToZ3("(push)\n")
	      val _ = (z3StackSize := ((! z3StackSize) + 1))
	  in
	      ()
	  end
      else
	  raise Z3NotStarted

  fun pop () = 
      if (z3Started()) then
	  if ((! z3StackSize) <= 0) then
	      raise Z3InvalidStack
	  else
	      let
		  val _ = printToZ3("(pop)\n")
		  val _ = (z3StackSize := ((! z3StackSize) - 1))
	      in
		  ()
	      end
      else
	  raise Z3NotStarted

end

(* Tests *)
(*
val () = (print "Testing Z3 boot...\n")
val false = Conditions.z3Started()
val () = Conditions.StartZ3()
val true = Conditions.z3Started()

val () = (print "Testing Z3 assert...\n")
val () = Conditions.push()
val () = (print "ASSERT(true)[true]\n")
val () = Conditions.assert(AAst.BoolConst(true))
val true = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(false)[false]\n")
val () = Conditions.assert(AAst.BoolConst(false))
val false = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(testvarname = 10)[true]\n")
val () = Conditions.assert(AAst.Op(Ast.EQ, [AAst.Local(Symbol.new("testvarname"), 0),AAst.IntConst(Word32.fromInt 10)]))
val true = Conditions.check()
val () = (print "ASSERT(testvarname != 10)[false]\n")
val () = Conditions.assert(AAst.Op(Ast.NOTEQ, [AAst.Local(Symbol.new("testvarname"), 0),AAst.IntConst(Word32.fromInt 10)]))
val false = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(t1 = 10)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.EQ,
		 [AAst.Local(Symbol.new("t1"), 0),
			    AAst.IntConst(Word32.fromInt 10)]))
val true = Conditions.check()
val () = (print "ASSERT(t2 = 10)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.EQ,
		 [AAst.Local(Symbol.new("t2"), 0),
			    AAst.IntConst(Word32.fromInt 10)]))
val true = Conditions.check()
val () = (print "ASSERT(t1*t2 = 100)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.EQ,
		 [AAst.Op(Ast.TIMES,
			  [AAst.Local(Symbol.new("t1"), 0),
				     AAst.Local(Symbol.new("t2"), 0)]),
		  AAst.IntConst(Word32.fromInt 100)]))
val true = Conditions.check()
val () = (print "ASSERT(t1*t2 != 100)[false]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.NOTEQ,
		 [AAst.Op(Ast.TIMES,
			  [AAst.Local(Symbol.new("t1"), 0),
				     AAst.Local(Symbol.new("t2"), 0)]),
		  AAst.IntConst(Word32.fromInt 100)]))
val false = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(100 > 10)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.GREATER,
		 [AAst.IntConst(Word32.fromInt 100),
		  AAst.IntConst(Word32.fromInt 10)]))
val true = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT((512 ^ 1023) = 511)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.EQ,
		 [AAst.Op(Ast.XOR,
			  [AAst.IntConst(Word32.fromInt 512),
			   AAst.IntConst(Word32.fromInt 1023)]),
		  AAst.IntConst(Word32.fromInt 511)]))
val true = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(~256 = -257)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.EQ,
		 [AAst.Op(Ast.COMPLEMENT,
			  [AAst.IntConst(Word32.fromInt 256)]),
		  AAst.IntConst(Word32.fromInt ~257)]))
val true = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(true && false)[false]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.LOGAND,
		 [AAst.BoolConst(true),
		  AAst.BoolConst(false)]))
val false = Conditions.check()
val () = Conditions.pop()
val () = Conditions.push()
val () = (print "ASSERT(true || false)[true]\n")
val () = Conditions.assert(
	 AAst.Op(Ast.LOGOR,
		 [AAst.BoolConst(true),
		  AAst.BoolConst(false)]))
val true = Conditions.check()
val () = Conditions.pop()
		 

val () = (print "Testing Z3 destroy...\n")
val () = Conditions.EndZ3()
val false = Conditions.z3Started()

val () = (print "Z3 tests finished!\n")
*)
