(* C0 Compiler
 * Constraint store for VCGen
 * Jason Chow
 * Matthew McKay <mjmckay@andrew.cmu.edu>
 *)

signature CONDITIONS =
sig
    exception Unimplemented of string

    (* Tries to assert a boolean expression. *)
    val assert : (Ast.tp SymMap.map) -> (AAst.aexpr -> unit)

    (* Checks if the current assertions on the stack are satisfiable or not.
     * Returns true if satisfiable, false if not satisfiable or unknown.
     *
     * Should really return a datatype containing more information, but just use
     * a boolean for now. *)
    val check : unit -> bool

    (* Stores the current set of assertions for later use *)
    val push : unit -> unit

    (* Updates the assertions to be the most recently stored  *)
    val pop : unit -> unit

    (* Resets the Z3 stack to empty (no assertions) *)
    val reset : unit -> unit

    (* Starts the Z3 process *)
    val StartZ3 : unit -> unit

    (* Kills the Z3 process *)
    val EndZ3 : unit -> unit

    (* Returns if the Z3 process is started or not *)
    val z3Started : unit -> bool

end

structure Conditions :> CONDITIONS =
struct

(*Debug flags*)
val print_local_var_list = false
val print_z3_print = false
val print_z3_errors = false
val print_z3_read = false
val print_raw_expr = false

val z3proc : ((TextIO.instream * TextIO.outstream) *
	      (TextIO.instream, TextIO.outstream) Unix.proc) option ref
  = ref NONE
val z3StackSize : int ref = ref 0
val declaredVariables : LocalSet.set ref = ref LocalSet.empty

exception Z3NotStarted
exception Z3InvalidStack
exception Unimplemented of string

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
	    ignore (Unix.reap(p));
	    (z3proc := NONE);
	    ()
	end
    else
	raise Z3NotStarted
fun printToZ3 (str : string) =
    let
	val SOME ((istr, ostr), p) = !z3proc
    in
	(if print_z3_print then print(">> " ^ str) else ());
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
	     (if print_z3_errors then print("<< " ^ str) else ());
	     readFromZ3()
	    )
	else
	    (
	     (if print_z3_print then print("<< " ^ str) else ());
	     str
	    )
    end

fun assert(map : Ast.tp SymMap.map)(e) =
    if (z3Started()) then
	let
	    fun localName(AAst.Local(sym, gen)) =
		    ((Symbol.nameFull(sym)) ^ "_" ^ (Int.toString(gen)))
              | localName _ = raise Unimplemented "localName"

	    fun localType(e as AAst.Local(sym, gen)) =
                (case SymMap.find(map, sym) of
                   SOME tp => (
                   case tp of
                     Ast.Int => SOME "(_ BitVec 32)"
                   | Ast.Bool => SOME "Bool"
                   | Ast.String => raise Unimplemented "localType"
                   | Ast.Char => raise Unimplemented "localType"
                   | Ast.Pointer(_) => raise Unimplemented "localType"
                   | Ast.Array(_) => raise Unimplemented "localType"
                   | Ast.TypeName(_) => NONE
                   | Ast.Void => NONE
                   | Ast.Any => NONE
                   | _ => raise Unimplemented "localType"
                   )
                 | _ => (* Default to int32 *)
		   SOME "(_ BitVec 32)")
              | localType _ = raise Unimplemented "localType"

            fun localArrayLengthName(e as AAst.Local(sym, gen)) =
                (localName(e) ^ "_length")
              | localArrayLengthName _ = raise Unimplemented "localArray"

            fun localLenToLocal(AAst.Length(y as AAst.Local(sym, gen))) = 
                (AAst.Local(Symbol.symbol(localArrayLengthName(y)), gen))
              | localLenToLocal _ = raise Unimplemented "localLen"

	    fun getNewLocalList(e : AAst.aexpr list) : AAst.aexpr list =
		case e of
		    [] => []
		  | x::xs => (
		    case x of
            AAst.Local(s) =>
              if LocalSet.member(!declaredVariables,s)
                then []
                else (declaredVariables := LocalSet.add(!declaredVariables,s);[x])
		      | AAst.Op(_, exprlist) => getNewLocalList(exprlist)
		      | AAst.Call(_, exprlist) => getNewLocalList(exprlist)
		      | AAst.IntConst(_) => []
		      | AAst.BoolConst(_) => []
		      | AAst.StringConst(_) => []
		      | AAst.CharConst(_) => []
		      | AAst.Alloc(_) => []
		      | AAst.Null => []
		      | AAst.Result => []
		      | AAst.Length(AAst.Local(sym, gen)) => [localLenToLocal(x)]
		      | AAst.Old(AAst.Local(sym, gen)) => raise Unimplemented "localList"
		      | AAst.AllocArray(_, expr) => getNewLocalList([expr])
		      | AAst.Select(expr, _) => getNewLocalList([expr])
		      | AAst.MarkedE(mk) => getNewLocalList([Mark.data(mk)])
                      | _ => []
		    )@getNewLocalList(xs)

	    fun assert_expr(e : AAst.aexpr) =
		case e of
		    AAst.Local((sym, gen)) => localName(e)
		  | AAst.Op(oper, exprlist) => (
		    case oper of
			Ast.SUB => raise Unimplemented "assert_expr sub" (* Not seen *)
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
		      | Ast.DEREF => raise Unimplemented "assert_expr deref"
		      | Ast.TIMES => (
			let
			    val [x,y] = exprlist
			in
			    "(bvmul " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
			end
			)
		      | Ast.DIVIDEDBY => ( (*DEFAULT TO SIGNED DIVISION*)
			let
			    val [x,y] = exprlist
			in
			    "(bvsdiv " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
			end)
		      | Ast.MODULO => ( (*DEFAULT TO SIGNED MODULUS*)
			let
			    val [x,y] = exprlist
			in
			    "(bvsrem " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
			end)
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
		      | Ast.LESS => ( (*DEFAULT TO SIGNED COMPARISION*)
			let
			    val [x,y] = exprlist
			in
			    "(bvslt " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
			end)
		      | Ast.LEQ => ( (*DEFAULT TO SIGNED COMPARISION*)
			let
			    val [x,y] = exprlist
			in
			    "(bvsle " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
			end)
		      | Ast.GREATER => ( (*DEFAULT TO SIGNED COMPARISION*)
			let
			    val [x,y] = exprlist
			in
			    "(bvsgt " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ ")"
			end)
		      | Ast.GEQ => ( (*DEFAULT TO SIGNED COMPARISION*)
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
		      | Ast.COND => (
			let
			    val [x,y,z] = exprlist
			in
			    "(ite " ^ (assert_expr(x)) ^ " " ^ (assert_expr(y)) ^ " " ^ (assert_expr(z)) ^ ")"
			end)
		    )
		  | AAst.Call(sym, exprlist) => raise Unimplemented "assert_expr call" (* Most likely not seen *)
		  | AAst.IntConst(word) => (
		    "(_ bv" ^ Word32.fmt(StringCvt.DEC)(word) ^ " 32)")
		  | AAst.BoolConst(bool) => (Bool.toString bool)
		  | AAst.StringConst(str) => raise Unimplemented "assert_expr string" (* Not arithmetic *)
		  | AAst.CharConst(ch) => raise Unimplemented "assert_expr char" (* Not arithmetic *)
		  | AAst.Alloc(tp) => raise Unimplemented "assert_expr alloc" (* No pointers *)
		  | AAst.Null => raise Unimplemented "assert_expr null" (* No pointers *)
		  | AAst.Result => raise Unimplemented "assert_expr result" (* Not seen *)
		  | AAst.Length(AAst.Local(sym, gen)) => assert_expr(localLenToLocal(e)) (* Treat as a _length variable *)
		  | AAst.Length(AAst.MarkedE m) =>
          (case Mark.data m of
            AAst.Local(sym,gen) =>
              assert_expr(localLenToLocal(AAst.Length(Mark.data m))) (* Treat as a _length variable *)
          | _ => raise Unimplemented "assert_expr length")
		  | AAst.Old(AAst.Local(sym, gen)) => raise Unimplemented "assert_expr old" (* ??? *)
		  | AAst.Old(AAst.MarkedE m) => raise Unimplemented "assert_expr old" (* ??? *)
		  | AAst.AllocArray(tp,expr) => raise Unimplemented "assert_expr allocarray" (* Not seen *)
		  | AAst.Select(expr,sym) => raise Unimplemented "assert_expr select" (* Struct fields, we'll deal with this later *)
		  | AAst.MarkedE(mk) => assert_expr(Mark.data(mk))
		  | _ => raise Unimplemented "assert_expr base case"

	    val local_list = getNewLocalList([e])
	    fun printList(ls) =
		case ls of
		    [] => ()
		  | [x] => (print(localName(x));())
		  | x::xs => (print(localName(x) ^ ", ");printList(xs);())
	    fun declareList(ls) =
		case ls of
		    [] => ()
		  | x::xs => (
                    (case localType(x) of
                       SOME y => (printToZ3("(declare-const " ^ (localName(x)) ^ " " ^ y ^ ")\n"))
                     | _ => ());
                    declareList(xs);())
	    val raw_expr = assert_expr(e)
	in
	    (if print_local_var_list then
		 case local_list of
		     [] => ()
		   | _ => (
		     print("Local variable list: {");
		     printList(local_list);
		     print("}\n"))
	     else ());
	    (if print_raw_expr then
		 print("raw_expr: " ^ (raw_expr) ^ "\n")
	     else ());
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
	    val str = (printToZ3("(check-sat)\n");readFromZ3())
	in	  
	    case String.compare(str, "sat\n") of
		EQUAL => true | _ => false
	end
    else
	raise Z3NotStarted

fun push () = 
    if (z3Started()) then
	(printToZ3("(push)\n");
	 (z3StackSize := ((! z3StackSize) + 1));
	 ())
    else
	raise Z3NotStarted

fun pop () = 
    if (z3Started()) then
	if ((! z3StackSize) <= 0) then
	    raise Z3InvalidStack
	else
	    (printToZ3("(pop)\n");
	     (z3StackSize := ((! z3StackSize) - 1));
	     ())
    else
	raise Z3NotStarted

fun reset () = 
    if (z3Started()) then
	if ((! z3StackSize) < 0) then
	    raise Z3InvalidStack
	else
	    (printToZ3("(reset)\n");
	     (z3StackSize := 0);
       (declaredVariables := LocalSet.empty);
	     ())
    else
	raise Z3NotStarted
end





(* Tests *)

val () = let
    val do_tests = false
    val print_z3_test_verbose = false
    fun print(str) =
	if print_z3_test_verbose then
	    TextIO.print(str)
	else
	    ()
    fun break() =
	((print "--------------------\n");
	 Conditions.reset())
    val assert =
        let
          val mp = SymMap.empty
        in
          Conditions.assert(mp)
        end
in
    if do_tests then
	let
	    val false = ((print "Testing Z3 initial state...\n");
			 Conditions.z3Started())
	    val true = ((print "Testing Z3 boot...\n");
			Conditions.StartZ3();
			Conditions.z3Started())
		       
	    val true = ((print "Testing Z3 asserts and checks...\n");
			(print "==ASSERT(expr)[expected]==\n");
			break();
			(print "  ASSERT(true)[true]\n");
			assert(AAst.BoolConst(true));
			Conditions.check())
	    val false = ((print "  ASSERT(false)[false]\n");
			 assert(AAst.BoolConst(false));
			 Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(t0 = 10)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Local(Symbol.symbol("t0"), 0),
				 AAst.IntConst(Word32.fromInt 10)]));
			Conditions.check())
	    val false = ((print "  ASSERT(t0 != 10)[false]\n");
			 assert(
			 AAst.Op(Ast.NOTEQ,
				 [AAst.Local(Symbol.symbol("t0"), 0),
				  AAst.IntConst(Word32.fromInt 10)]));
			 Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(t1 = 10)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Local(Symbol.symbol("t1"), 0),
				 AAst.IntConst(Word32.fromInt 10)]));
			Conditions.check())
	    val true = ((print "  ASSERT(t2 = 10)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Local(Symbol.symbol("t2"), 0),
				 AAst.IntConst(Word32.fromInt 10)]));
			Conditions.check())
	    val true = ((print "  ASSERT(t1*t2 == 100)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.TIMES,
					 [AAst.Local(Symbol.symbol("t1"), 0),
					  AAst.Local(Symbol.symbol("t2"), 0)]),
				 AAst.IntConst(Word32.fromInt 100)]));
			Conditions.check())
	    val false = ((print "  ASSERT(t1*t2 != 100)[false]\n");
			 assert(
			 AAst.Op(Ast.NOTEQ,
				 [AAst.Op(Ast.TIMES,
					  [AAst.Local(Symbol.symbol("t1"), 0),
					   AAst.Local(Symbol.symbol("t2"), 0)]),
				  AAst.IntConst(Word32.fromInt 100)]));
			 Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(100 > 10)[true]\n");
			assert(
			AAst.Op(Ast.GREATER,
				[AAst.IntConst(Word32.fromInt 100),
				 AAst.IntConst(Word32.fromInt 10)]));
			Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT((512 ^ 1023) = 511)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.XOR,
					 [AAst.IntConst(Word32.fromInt 512),
					  AAst.IntConst(Word32.fromInt 1023)]),
				 AAst.IntConst(Word32.fromInt 511)]));
			Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(~256 == -257)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.COMPLEMENT,
					 [AAst.IntConst(Word32.fromInt 256)]),
				 AAst.IntConst(Word32.fromInt ~257)]));
			Conditions.check())
	    val () = break()
	    val false = ((print "  ASSERT(true && false)[false]\n");
			 assert(
			 AAst.Op(Ast.LOGAND,
				 [AAst.BoolConst(true),
				  AAst.BoolConst(false)]));
			 Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(true || false)[true]\n");
			assert(
			AAst.Op(Ast.LOGOR,
				[AAst.BoolConst(true),
				 AAst.BoolConst(false)]));
			Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(t2 = 0)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Local(Symbol.symbol("t2"), 0),
				 AAst.IntConst(Word32.fromInt 0)]));
			Conditions.check())
	    val true = ((print "  ASSERT(t2 == 0 ? true : false)[true]\n");
			assert(
			AAst.Op(Ast.COND,
				[AAst.Op(Ast.EQ,
					 [AAst.Local(Symbol.symbol("t2"), 0),
					  AAst.IntConst(Word32.fromInt 0)]),
				 AAst.BoolConst(true),
				 AAst.BoolConst(false)]));
			Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(10 % 3 == 1)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.MODULO,
					 [AAst.IntConst(Word32.fromInt(10)),
					  AAst.IntConst(Word32.fromInt(3))]),
				 AAst.IntConst(Word32.fromInt(1))]));
			Conditions.check())
	    val true = ((print "  ASSERT(-10 % 3 == -1)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.MODULO,
					 [AAst.IntConst(Word32.fromInt(~10)),
					  AAst.IntConst(Word32.fromInt(3))]),
				 AAst.IntConst(Word32.fromInt(~1))]));
			Conditions.check())
	    val true = ((print "  ASSERT(10 % -3 == 1)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.MODULO,
					 [AAst.IntConst(Word32.fromInt(10)),
					  AAst.IntConst(Word32.fromInt(~3))]),
				 AAst.IntConst(Word32.fromInt(1))]));
			Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(10 / 3 == 3)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.DIVIDEDBY,
					 [AAst.IntConst(Word32.fromInt(10)),
					  AAst.IntConst(Word32.fromInt(3))]),
				 AAst.IntConst(Word32.fromInt(3))]));
			Conditions.check())
	    val true = ((print "  ASSERT(-10 / 3 == -3)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.DIVIDEDBY,
					 [AAst.IntConst(Word32.fromInt(~10)),
					  AAst.IntConst(Word32.fromInt(3))]),
				 AAst.IntConst(Word32.fromInt(~3))]));
			Conditions.check())
	    val true = ((print "  ASSERT(-10 / -3 == 3)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Op(Ast.DIVIDEDBY,
					 [AAst.IntConst(Word32.fromInt(~10)),
					  AAst.IntConst(Word32.fromInt(~3))]),
				 AAst.IntConst(Word32.fromInt(3))]));
			Conditions.check())
	    val () = break()
	    val true = ((print "  ASSERT(\\length(A) = 10)[true]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Length(AAst.Local(Symbol.symbol("A"), 0)),
				 AAst.IntConst(Word32.fromInt(10))]));
			Conditions.check())
	    val false = ((print "  ASSERT(\\length(A) == 11)[false]\n");
			assert(
			AAst.Op(Ast.EQ,
				[AAst.Length(AAst.Local(Symbol.symbol("A"), 0)),
				 AAst.IntConst(Word32.fromInt(11))]));
			Conditions.check())
	    val () = break()
	    val false = ((print "Testing Z3 destroy...\n");
			 Conditions.EndZ3();
			 Conditions.z3Started())
	in
	    print "Z3 tests finished!\n"
	end
    else ()
end

