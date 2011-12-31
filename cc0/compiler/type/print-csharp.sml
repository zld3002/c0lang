structure PrintCSharp =
struct

  structure A = Ast

  exception Error of string

  (* A map from defined names to their original types, since C# has no typedef*)
  val typedefs : A.tp Symbol.table ref = ref Symbol.empty

  (* A map that finds the classname to put in front of functions and structs
     defined in other files, since C# doesn't have a global namespace like C0 *)
  val libmap : string Symbol.table ref = ref Symbol.empty

  (* These are used to identify structs which are referenced but not defined
     and provide them with a simple definition at the end to placate gmcs *)
  val local_structs : Symbol.set ref = ref Symbol.null
  val missing_structs : Symbol.set ref = ref Symbol.null

  (* This is a Main() method included in all programs which then calls the
     main() function that the programmer wrote. This is used to handle 
     exceptions that might be raised by the progam and also to interface with
     the test driver in the way that the driver expects. *)
  val main_string = "public static void Main(){\n" ^
                    "\tint result = 0;\n" ^
                    "\tstring r_file = System.Environment.GetEnvironmentVariable(\"C0_RESULT_FILE\");\n" ^
                    "\tif (r_file == null)\n" ^
                    "\t\tSystem.Console.WriteLine(main());\n" ^
                    "\telse\n" ^
                    "\t{\n" ^
                    "\t\tint status = 0;\n" ^
                    "\t\ttry{\n" ^
                    "\t\t\tresult = main();\n" ^ "\t\t}\n" ^ 
                    "\t\tcatch(NullReferenceException) {status = 1;}\n"^
                    "\t\tcatch(IndexOutOfRangeException) {status = 1;}\n"^
                    "\t\tcatch(DivideByZeroException) {status = 2;}\n" ^
                    "\t\tcatch(ArithmeticException) {status = 2;}\n" ^
                    "\t\tcatch(AbortException) {status = 3;}\n"^
                    "\t\tcatch(Exception) {status = 4;}\n" ^
                    "\t\tFileStream fs = new FileStream(r_file, FileMode.OpenOrCreate, FileAccess.Write);\n" ^
                    "\t\tBinaryWriter writer = new BinaryWriter(fs);\n" ^
                    "\t\twriter.Write((byte)status);\n" ^
                    "\t\twriter.Write(result);\n" ^
                    "\t\twriter.Close();\n" ^
                    "\t\tfs.Close();\n" ^
                    "\t}\n" ^
                    "\tSystem.Environment.Exit(0);\n}\n\n"

  (* This method is used to duplicate the functionality of the assert construct
     in C0 in terms of printing messages and then aborting the program *)
  val assert_string = "public static void assert(bool b, string message){\n" ^ 
                       "\tif (b) return;\n" ^ 
                       "\tSystem.Console.WriteLine(message);\n" ^
                       "\tSystem.Console.WriteLine(\"Aborted\");\n" ^
                       "\tthrow new AbortException();\n}\n\n"
                       (*"\tSystem.Environment.Exit(-1);\n}\n\n" *)

  val abort_string = "public class AbortException : Exception {}\n\n"
                     
  (* Used to trick gmcs into not recognizing static division by 0, which it 
     refuses to compile but C0 allows *)
  val zero_string = "public static int zero()\n{\n" ^
                    "\treturn 0;\n}\n\n"

  (* This is wrapped around stand-alone expression statements so that gmcs
     will compile pointless-but-legal-in-C0 stand-alone expressions *)
  val id_string = "public static object id(object x){\n" ^
                  "\treturn x;\n}\n\n"

  (* This is used to simulate statically allocating an array of negative size,
     since this is (statically) legal in C0 but always returns NULL *)
  val nullref_string = "public static object null_ref(){\n" ^ 
                       "\tthrow new NullReferenceException();\n" ^
                       "\treturn null;\n}\n\n"

  (* C# doesn't have pointers, so we had to get a bit creative with duplicating
     their behavior. Thankfully, we do have generic classes, so we can just
     have one pointer class rather than one for every type of pointer in the
     program. The value member of this class is accessed to get to what the 
     pointer points to. This does increase the number of dynamic  allocations
     that the program makes because the pointer variable itself must be 
     allocated, but this probably isn't noticable for the programs we are 
     likely to see here *)
  val pointer_string = "public class P<T> \n{\n" ^
                       "\tpublic T value;\n" ^
                       "\tpublic P(){}\n\n" ^
                       "\tpublic P(T init)\n" ^ 
                       "\t{\n" ^
                       "\t\tvalue = init;\n" ^
                       "\t}\n}\n\n"

  (* Include some C# libraries we need *)
  val using_string = "using System;\n" ^
                     "using System.IO;\n" ^
                     "using Mono.Unix.Native;\n\n"

  (* \? is a valid escape character in C but not C#, so we need this in
     addition to the String.toCString SML function to handle escapes right *)
  fun fix_question_marks s =
      let
          fun unescape ((#"\\")::(#"?")::l) = #"?"::unescape(l)
            | unescape (c::l) = c::unescape(l)
            | unescape [] = []

          val chars = String.explode s
          val newchars = unescape chars
      in
          String.implode newchars
      end

  (* Fill in skeleton definitions of structs which were referenced but
     never defined anywhere, since undefined types are ok in C0 but not C# *)
  fun make_missing_structs () =
      let
          fun make_class s = "public class _s_" ^ Symbol.name s ^ "{}"

          val missing = Symbol.listmems (!missing_structs)
          val newstructs = map make_class missing
      in
          String.concat newstructs
      end

  (* Return the default value for each type to initialize struct fields with *) 
  fun def_val A.Int = "0"
    | def_val A.Bool = "false"
    | def_val A.String = "\"\""
    | def_val A.Char = "'\\0'"
    | def_val (A.TypeName(name)) =
        let
            val typeOpt = Symbol.look (!typedefs) name
        in
            case typeOpt
              of SOME(tau) => def_val tau
               | NONE => "null"
        end
    | def_val _ = "null"

  fun pp_type A.Int = "int"
    | pp_type A.Bool = "bool"
    | pp_type A.String = "string"
    | pp_type A.Char = "char"
    | pp_type (A.Pointer tau) = "P<" ^ pp_type tau ^ ">"
    | pp_type (A.Array tau) = pp_type tau ^ "[]"
    | pp_type (A.StructName(name)) =
        let
            (* Since structs defined in libraries will be found in other
               classes, we might need to stick <classname>. in front of 
               references to a struct name. *)
            val libopt = Symbol.look (!libmap) name
            val s_str = "_s_" ^ Symbol.name name
        in
            case libopt
              of NONE =>
                   if (Symbol.member (!local_structs) name) then
                      s_str
                   else
                      (missing_structs := Symbol.add (!missing_structs) name; s_str)
               | SOME(libname) => libname ^ "." ^ s_str
        end 
    | pp_type (A.TypeName(name)) =
        let
            (* C# lacks typedefs, so revert defined types to their aliases *)
            val typeOpt = Symbol.look (!typedefs) name
        in
            case typeOpt
              of SOME(tau) => pp_type tau
               | NONE => (print ("Unknown type: " ^ Symbol.name name ^ "\n"); Symbol.name name)
        end
    | pp_type A.Void = "void"
    | pp_type A.Any = raise Error "ANY type in AST"


  and construct_fields [] = ""
    | construct_fields ((A.Field(fname, tau,ext))::flist) =
       case tau
        of A.StructName(name) => 
            "\t" ^ Symbol.name fname ^ " = new " ^ pp_type tau ^ "();\n" ^ 
            construct_fields flist
         | A.TypeName(name) =>
            construct_fields (A.Field(name, Symbol.look' (!typedefs) name,ext)::flist)
         | _ => construct_fields flist


  and pp_field (A.Field(name, tau, _)) =
        "public " ^
        pp_type tau ^ " " ^
        Symbol.name name

  and pp_struct_def name [] = 
      (* Empty struct case *) 
      (local_structs := Symbol.add (!local_structs) name;
      (if (Symbol.member (!missing_structs) name) then 
          missing_structs := Symbol.remove (!missing_structs) name
       else
          ());
       "public class _s_" ^ Symbol.name name ^ "{}\n\n")
    | pp_struct_def name fields = 
      (local_structs := Symbol.add (!local_structs) name;
      (if (Symbol.member (!missing_structs) name) then 
          missing_structs := Symbol.remove (!missing_structs) name
       else
          ());
      "public class " ^
      "_s_" ^ Symbol.name name ^ "{\n" ^
      String.concatWith ";\n" (List.map pp_field fields) ^ ";\n" ^ 
      "\tpublic _s_" ^ Symbol.name name ^ "()\n\t{\n" ^
      construct_fields fields ^
      "\t}\n" ^
      "}\n\n")
      

  and pp_args args = "(" ^ (String.concatWith ", " (map pp_decl args)) ^ ")"

  (* This list is incomplete because some operators must be handled specially *)
  and pp_oper A.LOGNOT = "!"
    | pp_oper A.COMPLEMENT = "~"
    | pp_oper A.NEGATIVE = "-"
    | pp_oper A.DEREF = ".value"
    | pp_oper A.TIMES = "*"
    | pp_oper A.DIVIDEDBY = "/"
    | pp_oper A.MODULO = "%"
    | pp_oper A.PLUS = "+"
    | pp_oper A.MINUS = "-"
    | pp_oper A.SHIFTLEFT = "<<"
    | pp_oper A.SHIFTRIGHT = ">>"
    | pp_oper A.LESS = "<"
    | pp_oper A.LEQ = "<="
    | pp_oper A.GREATER = ">"
    | pp_oper A.GEQ = ">="
    | pp_oper A.EQ = "=="
    | pp_oper A.NOTEQ = "!="
    | pp_oper A.AND = "&"
    | pp_oper A.XOR = "^"
    | pp_oper A.OR = "|"
    | pp_oper A.LOGAND = "&&"
    | pp_oper A.LOGOR = "||"
    | pp_oper _ = raise Error "unexpected operator"

  (* The normal recursive type printing doesn't match what C# wants, so we
     handle that specially. *)
  and pp_array_alloc (A.Array(tau)) middle = (pp_array_alloc tau middle) ^ "[]"
    | pp_array_alloc (A.TypeName(name)) middle = pp_array_alloc (Symbol.look' (!typedefs) name) middle
    | pp_array_alloc tau middle = pp_type tau ^ middle

  (* Some cases are singled out to avoid making extraneous parentheses *)
  and pp_exp (A.Marked(e)) = pp_exp (Mark.data e)
    | pp_exp (A.Var(name)) = "_v_" ^ Symbol.name name
    | pp_exp (A.IntConst(n)) = 
              let
                  val s = LargeInt.toString (Word32.toLargeIntX n)
              in
                  (* gmcs doesn't like the standard representation of this
                     integer constant *)
                  if (n = 0w2147483648) then
                    "unchecked((int)0x80000000)"
                  else if (String.sub (s, 0) = #"~") then
                    "-" ^ String.extract (s, 1, NONE)
                  else
                    s
              end
    | pp_exp (A.StringConst(s)) = "\"" ^ (fix_question_marks (String.toCString s)) ^ "\""
    | pp_exp (A.CharConst(c)) = "'" ^ Char.toCString(c) ^ "'"
    | pp_exp (A.True) = "true"
    | pp_exp (A.False) = "false"
    | pp_exp (A.Null) = "null"
    | pp_exp (A.FunCall (fname, args)) = 
             let
                 val libopt = Symbol.look (!libmap) fname
                 val f_str = Symbol.name fname
                 (* If this is a library call we need a classname prefix *)
                 val call_str = case libopt
                                  of NONE => f_str
                                   | SOME(libname) => libname ^ "." ^ f_str
             in
                call_str ^ "(" ^ 
                String.concatWith ", " (List.map pp_exp args) ^ ")" 
             end
    | pp_exp e =
      "(" ^ 
      (case e
         of A.OpExp (A.DEREF, [e]) => pp_exp e ^ ".value"
          | A.OpExp (A.COND, [c, etrue, efalse]) =>
               pp_exp c ^ " ? " ^ pp_exp etrue ^ ": " ^ pp_exp efalse
          | A.OpExp (A.SUB, [e1, e2]) => pp_exp e1 ^ "[" ^ pp_exp e2 ^ "]"
          | A.OpExp (A.DIVIDEDBY, [e1, e2]) =>
               pp_exp e1 ^ "/ (zero() +" ^ pp_exp e2 ^ ")"
          | A.OpExp (A.MODULO, [e1, e2]) =>
               pp_exp e1 ^ "% (zero() +" ^ pp_exp e2 ^ ")"
          | A.OpExp (oper, [e]) => pp_oper oper ^ pp_exp e
          | A.OpExp (oper, [e1, e2]) =>
               pp_exp e1 ^ " " ^ pp_oper oper ^ " " ^ pp_exp e2
          | A.OpExp (oper, _) => raise Error "Unhandled OpExp"
          | A.Select(e, fname) => pp_exp e ^ "." ^ Symbol.name fname
          | A.Alloc (tau as A.StructName(name)) =>
                   "new P<" ^ pp_type tau ^ ">(new " ^ pp_type tau ^ "())"
          | A.Alloc (A.TypeName(name)) => 
               pp_exp (A.Alloc(Symbol.look' (!typedefs) name))
          | A.Alloc (tau) => "new P<" ^ pp_type  tau ^ ">(" ^ def_val tau ^ ")"
          | A.AllocArray (tau, A.Marked(e)) =>
               pp_exp (A.AllocArray(tau, Mark.data e))
          (* Statically allocating negative sized arrays is legal in C0 but
             not C#, so we just jump straight to the null pointer that it
             will result in *)
          | A.AllocArray (tau, n as A.OpExp(A.NEGATIVE, [A.IntConst(num)])) => 
               if num >= 0w0 then
                  "null_ref()"
               else
                  "new " ^ pp_array_alloc tau ("[" ^ pp_exp n ^ "]")
          | A.AllocArray (tau, num) =>
               "new " ^ pp_array_alloc tau ("[" ^ pp_exp num ^ "]")
          | A.Result => raise Error "Result in PrintCS"
          | A.Length (e) => pp_exp e ^ ".Length"
          | A.Old (e) => raise Error "Old in PrintCS"
          | _ => raise Error "Unhandled expression in PrintCS"
      ) ^ 
      ")"

  and pp_stringlist nil = "\"\""
    | pp_stringlist (e::nil) = pp_exp e
    | pp_stringlist (e::es) =
      pp_exp e ^ " + " ^ pp_stringlist es

  (* The parser often builds an AST with more nested Seqs than are really 
     necessary. Since we often need to wrap {} around these to get proper
     scoping, this leads to really ugly code without the following function
     to minimize this. *)
  and compress_seqs decls stms =
      case stms
        of A.Seq(decls2, stms2)::stms3 => compress_seqs (decls@decls2) (stms2@stms3)
         | A.Anno(_)::stms2 => compress_seqs decls stms2
         | A.Markeds(s)::stms2 => compress_seqs decls ((Mark.data s)::stms2)
         | _ => (decls, stms)

  and pp_decl (A.VarDecl(name, tau, NONE, _)) =
        pp_type tau ^" _v_"^ Symbol.name name
    | pp_decl (A.VarDecl(name, tau, SOME(e),_)) = 
        pp_type tau ^ " " ^
        "_v_" ^ Symbol.name name ^ " = " ^
        pp_exp e

  (* Wraps up the bodies of control statements with properly indented braces *)
  and brace indent str = "\n" ^ indent ^ "{\n" ^ str ^ indent ^ "}\n"

  and pp_stm indent s = 
      case s
        of A.Assign (NONE, lval, rval) => 
              indent ^ pp_exp lval ^ " = "^ pp_exp rval ^ ";\n"
         | A.Assign (SOME(oper), lval, rval) =>
              indent ^ pp_exp lval ^" "^ pp_oper oper ^"= "^ pp_exp rval ^";\n"
         | A.Exp (A.Marked(e)) =>
              pp_stm indent (A.Exp(Mark.data e))
         | A.Exp (e as A.FunCall(_,_)) =>
              indent ^ pp_exp e ^ ";\n"
         | A.Exp (e) =>
              indent ^ "id(" ^ pp_exp e ^ ");\n"
         | A.Seq ([], stms) => 
              String.concat (List.map (pp_stm indent) stms)
         | A.Seq (decls, stms) => 
            let
                val (newdecls, newstms) = compress_seqs decls stms
            in
              indent ^ "{\n" ^ indent ^ "\t" ^ 
              String.concatWith (";\n\t"^indent) (List.map pp_decl newdecls)^
              ";\n" ^
              String.concat (List.map (pp_stm (indent^"\t")) newstms) ^
              indent ^ "}\n"
            end
         | A.StmDecl(decl) =>
              indent ^ pp_decl decl ^ ";\n"
         | A.If (e, s_true, s_false) =>
              let
                  val cond_str  = indent ^ "if (" ^ pp_exp e ^ ")"
                  val true_str  = brace indent (pp_stm (indent ^ "\t") s_true)
                  val false_str = pp_stm (indent ^ "\t") s_false
              in
                 if (String.size false_str = 0) then
                    cond_str ^ true_str
                 else
                    cond_str ^ true_str ^ indent ^"else"^ brace indent false_str
              end
         | A.While (e, _, s) =>
              indent ^ "while (" ^ pp_exp e ^ ")" ^
              brace indent (pp_stm (indent^"\t") s)
         | A.For (init, cond, update, body) =>
              raise Error "For loop in PrintCS"
         | A.Continue =>
              indent ^ "continue;\n"
         | A.Break =>
              indent ^ "break;\n"
         | A.Return (NONE) =>
              indent ^ "return;\n"
         | A.Return (SOME(e)) =>
              indent ^ "return " ^ pp_exp e ^ ";\n"
	 | A.Assert (e, e2s) =>
	      indent ^ "assert(" ^ pp_exp e ^ ", " ^ pp_stringlist e2s ^ ");\n"
	 (* 
         | A.Assert (e, []) =>
              indent ^ "assert(" ^ pp_exp e ^ ", \"\");\n"
         | A.Assert (e, [e2]) =>
              indent ^ "assert(" ^ pp_exp e ^ ", " ^ pp_exp e2 ^ ");\n"
         *)
         | A.Anno(_) => 
              "" (* If an Anno is present, it means debug mode is off *)
         | A.Markeds(ms) =>
              pp_stm indent (Mark.data ms)
     

  and pp_fun name ret_type args body = 
        "public static " ^
        pp_type ret_type ^ " " ^ 
        Symbol.name name ^
        pp_args args ^ 
        (* The unchecked modifier prevents gmcs from complaining
           about certain static integer operations that overflow *)
        "\n{unchecked{\n" ^
        (pp_stm "\t" body) ^
        "}}\n\n"

  (* When using a library, we have to account for C# not having a global 
     namespace like C0 does. The library code is contained in library classes,
     and calls to these classes within the program need to be modified to
     refer to these library classes. This builds the mapping from identifiers
     to the class they are contained in.*)
  and pp_uselib libname [] = ""
    | pp_uselib libname (A.Function(name,_,_,NONE,_,_,_)::gdecls) =
         (libmap := Symbol.bind (!libmap) (name, "_l_" ^ libname);
          pp_uselib libname gdecls)
    | pp_uselib libname ((f as A.Function(name,_,_,SOME(_),_,_,_))::gdecls) =
          pp_gdecl f ^ pp_uselib libname gdecls
    | pp_uselib libname ((gdecl as A.Struct (name, SOME(fields),_,_))::gdecls) =
         (libmap := Symbol.bind (!libmap) (name, "_l_" ^ libname);
          pp_gdecl gdecl ^ pp_uselib libname gdecls)
    | pp_uselib libname ((gdecl as A.Struct (name, NONE,_,_))::gdecls) =
          (libmap := Symbol.bind (!libmap) (name, "_l_" ^ libname);
           pp_uselib libname gdecls)
    | pp_uselib libname ((gdecl as A.TypeDef (name, tau,_))::gdecls) =
          (typedefs := Symbol.bind (!typedefs) (name, tau);
           pp_uselib libname gdecls)
    | pp_uselib libname (gdecl::gdecls) = 
         pp_gdecl gdecl ^ pp_uselib libname gdecls

  and pp_gdecl (A.Struct (name, SOME(fields), _, _)) =
         pp_struct_def name fields
    | pp_gdecl (A.Struct (name, NONE, _, _)) = "// " ^ Symbol.name name ^ "\n"
    | pp_gdecl (A.TypeDef (name, tau, _)) =
         (typedefs := Symbol.bind (!typedefs) (name, tau); "")
    | pp_gdecl (A.Function (name, rtype, args, SOME(body), specs, is_extern,_))=
         pp_fun name rtype args body
    | pp_gdecl (A.Function (name, rtype, args, NONE, specs, is_extern, ext)) =
         "// " ^ Symbol.name name ^ "\n\n"
    | pp_gdecl (A.Pragma (A.UseLib(name, SOME(gdecls)),_)) =
         let
             val libstring = pp_uselib name gdecls
         in
             libstring
         end
    | pp_gdecl (A.Pragma (A.UseLib(name, NONE),_)) = ""
    | pp_gdecl (A.Pragma (A.UseFile(name, SOME(gdecls)),_)) =
         pp_gdecls gdecls
    | pp_gdecl (A.Pragma (A.UseFile(name, NONE),_)) = ""
    | pp_gdecl (A.Pragma (A.Raw(pname, pargs), _)) = ""

  and pp_gdecls [] = ""
    | pp_gdecls (f::l) = pp_gdecl f ^ pp_gdecls l

  (* Join all of the extra C# stuff together with the translated program to
     produce a compilable file *)
  and pp_program (lib_headers, program) = 
        using_string ^
        pointer_string ^ 
        abort_string ^ 
        "public class C0Program{\n\n" ^
        pp_gdecls lib_headers ^
        pp_gdecls program ^
        main_string ^ 
        assert_string ^
        zero_string ^
        id_string ^
        nullref_string ^
        make_missing_structs () ^
        "}"


end
