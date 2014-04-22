structure Gcl = struct

type ident = Symbol.symbol
type structname = ident 

(*NOTE: reversed from normal syntax, so (sn, [f,g,h]) represents sn.h.g.f *)
type field = structname * (ident list)

fun compareField ((s1,f1), (s2,f2)) =
   List.collate Symbol.compare (s1 :: (rev f1), s2 :: (rev f2))

datatype tp =
      Int                 (* int *)
    | Bool                (* bool *)
    | String              (* string *)
    | Char                (* char *)
    | Pointer of tp       (* tp* *)
    | Array of tp         (* tp[] *)
    | StructName of ident (* struct s *)
    | Void                (* aka unit type *) 
    
datatype relop = Less | Greater | Eq | Leq | Geq | Neq

datatype valop = 
    Complement | Negation | Addition | Subtract 
  | Mult | Div | Mod | LShift | RShift | Bitor | Bitand | Bitxor
  | Or | And | Not | Cond  (* Note: not short circuiting *)
  | Length
  | IntConst of Word32.word
  | StringConst of string
  | PureCall of ident * tp (* function name, return type *)
  | CharConst of char
  | BoolConst of bool
  | Nondet  (* nondeterministic boolean expression *)

(* Expressions are side-effect-free but may depend on the values in the heap. *)
datatype expr = 

  (*Values*)
    Var of ident * tp
  | ValOp of valop * expr list
  | Rel of relop * tp * expr * expr (* tp is type of the two exprs *)

  (*Heap*)
  | Sub of expr * expr * tp
  | Null of tp                      (* tp is the pointed to type, so
                                       Null(Int) : Pointer(Int) *)
  | Select of expr * field * tp
  | Deref of expr * tp              (* tp is the result, so this is well typed:
                                       Deref(Var("p",Pointer(Int)), Int)*)
                                       
  
(* Right hand sides of assignments statements. Note the right hand side is
   executed first (which cannot affect local variables, but could affect the heap)
   *)
datatype rhs = Expr of expr                (* e *)
             | Alloc of tp                 (* alloc(t) *)
             | AllocArray of tp * expr     (* alloc_array(t, n) *)
             | Call of ident * expr list   (* f(e0, e1, e2) *)
             
(* Possible LHS of assignments. Note that each only depends on variables, and 
   thus compound assignments such as p->next->data = 3; must be translated to
   single assignment forms. This forces the translation to specify the ordering
   of reads/writes to memory and updates to local variables. *)
datatype lhs = Local of ident              (* x := ... *)
             | Field of ident * field      (* p->f := ... *)
             | Cell of ident               (* *p := ... *)
             | ArrayElem of ident * ident  (* a[i] := ... *)
             
type label = int


datatype stmt =
    If of expr * stmt * stmt
  | While of stmt * expr * anno * stmt
  | Assume of expr
  | Assert of expr
  | Check of anno
  | Assign of lhs * rhs
  | Block of int * stmt
  | Break of int
  | Seq of stmt list
  | Comment of string
  | LabeledS of int * stmt

and anno = Anno of stmt * stmt * stmt (* well formed, assertion, assumption *)


datatype func =
   Function of tp * tp SymMap.map * (ident * tp) list * anno * stmt * anno
   (*return type, locals, formals, requires, body, ensures *)












(* This stuff should really be moved to it's own module. *)

fun tp_of e = 
  case e of
  (*Values*)
    Var(v, tp) => tp
  | ValOp(CharConst _,_) => Char
  | ValOp(StringConst _,_) => String
  | ValOp(IntConst _,_) => Int
  | ValOp(And,_) => Bool
  | ValOp(Or,_) => Bool
  | ValOp(Not,_) => Bool
  | ValOp(Cond,[c,a,b]) => tp_of a
  | ValOp(Length,_) => Int
  | ValOp(PureCall (_,t), _) => t
  | ValOp _ => Int
  | Rel _ => Bool
  | Sub(a, i, tp) => tp
  | Null tp => tp
  | Select (s, (sn, f), tp) => tp
  | Deref (p, tp) => tp
    

 val pp_sym = Symbol.name
 fun isNop (Seq[]) = true
   | isNop _ = false
   
 fun pp_tp t = case t of
      Int => "int"
    | Bool => "bool"
    | String => "string"
    | Char => "char"
    | Pointer t=> pp_tp t ^ "*"
    | Array t => pp_tp t ^ "[]"
    | StructName s => "struct "^(pp_sym s)
    | Void => "void"
 fun pp_field (sn, fs) = String.concatWith "." (map pp_sym (rev fs))
 
 fun pp_expr e = case e of
    Var (v, _) => pp_sym v
  | ValOp(IntConst w,[]) => LargeInt.toString (Word32.toLargeIntX w)
  | ValOp(StringConst s,[]) => "\""^ String.toCString s ^"\""
  | ValOp(CharConst c, []) => "'"^Char.toCString c ^ "'"
  | ValOp(BoolConst true, []) => "true"
  | ValOp(BoolConst false, []) => "false"
  | ValOp(Nondet, []) => "*"
  | ValOp(PureCall (f, _), args) => pp_sym f^ "(" ^ String.concatWith ", " (map pp_expr args) ^ ")"
  | ValOp(oper, [x]) => 
      let val sym = case oper of 
         Complement => "~"
       | Negation => "-"
       | Not => "!"
       | Length => "\\length"
      in sym ^ pp_expr(x)
      end
  | ValOp(oper, [x,y]) => 
      let val sym = case oper of 
         Addition => "+"
       | Subtract => "-"
       | Bitand => "&"
       | Bitor => "|"
       | Bitxor => "^"
       | Mult => "*"
       | Div => "/"
       | Mod => "%"
       | LShift => "<<"
       | RShift => ">>"
       | Or => "||"
       | And => "&&" 
      in pp_expr x ^ sym ^ pp_expr y
      end
  | ValOp(Cond, [c,x,y]) => pp_expr c ^ "?" ^ pp_expr x ^ ":" ^ pp_expr y
    
  | Rel (oper, _, e1, e2) =>
      let val sym = case oper of 
         Leq => "<="
       | Geq => ">="
       | Eq => "=="
       | Neq => "!="
       | Less => "<"
       | Greater => ">"
      in (pp_expr e1)^" "^sym^" "^(pp_expr e2) end
  (*Heap*)
  | Sub (a, i,_) => pp_expr a ^ "[" ^ pp_expr i ^ "]"
  | Null(tp) => "NULL{" ^ pp_tp tp ^ "}"
  | Select (s,f,_) => "("^pp_expr s^")." ^ pp_field f 
  | Deref (e,_) => "*" ^ pp_expr e
  
 val tab = "  "
 
 fun pp_annoi i (Anno (wf, assert, assume)) = 
    "wfchck:\n"^(pp_stmti (i^tab) wf) ^"\n" ^
    "assert:\n"^(pp_stmti (i^tab) assert) ^"\n" ^
    "assume:\n"^(pp_stmti (i^tab) assume) ^"\n"
   
 and pp_stmti i s = case s of
   
    If (e,a,b) => 
        i ^ "if ("^pp_expr e^") {\n" ^ 
        (pp_stmti (i^tab) a) ^ "\n" ^
        (case isNop b of 
            true => i ^ "}"
          | false => i ^ "} else {\n" ^ (pp_stmti (i^tab) b) ^ "\n"^i^"}")
  | While (es, e, Anno inv, b) => 
        (case isNop es of 
            true =>i ^ "while("^pp_expr e^")"
          | false => i ^ "while\n"^pp_stmti (i^tab) es ^"\n"^i^"("^pp_expr e^")") ^
        (case (isNop (#1 inv), isNop (#2 inv),isNop (#3 inv)) of
            (true,true,true) => " "
          | _ => "\n" ^ i^"inv:\n"^(pp_annoi (i^tab) (Anno inv)) ^"\n"^i) ^ 
        ("{\n" ^ 
           (pp_stmti (i^tab) b) ^ "\n"^
          i ^ "}")
  | Assume e => i ^ "assume("^pp_expr e^")"
  | Assert e => i ^ "assert("^pp_expr e^")"
  | Check a => pp_annoi i a
  | Assign (lhs,rhs) => 
      let val l = case lhs of
                     Local v => pp_sym v
                   | Field (v,(sn,fs)) => pp_sym v ^ "->" ^
                                           String.concatWith "." (map pp_sym (rev fs)) 
                   | Cell (v) => "*"^pp_sym v
                   | ArrayElem (a,i) => pp_sym a ^ "["^pp_sym i^"]"
          val r = case rhs of 
                     Expr e => pp_expr e
                   | Alloc t => "alloc("^pp_tp t^")"
                   | AllocArray (t,e) => "alloc("^pp_tp t^","^pp_expr e^")"
                   | Call (f,args) => pp_sym f^"("^String.concatWith "," (map pp_expr args) ^")"
      in i ^ l^ " := " ^r end
  | Block (ii,ss) => i^"block (" ^ Int.toString ii ^ ") {\n"
                    ^ (pp_stmti (i^tab) ss) ^"\n" ^ i ^ "}"
  | Break ii => i ^ "break (" ^ Int.toString ii ^ ")"
  | Seq [] => i^"//nop"
  | Seq ss => String.concatWith "\n" (map (pp_stmti i) ss)
  | Comment c => i ^ "/* " ^ c ^ " */"
  | LabeledS (l,s) =>
  (* i ^ "// stmt "^ (Int.toString l) ^":\n"^pp_stmti (i^tab) s
  ^ "\n" ^ i ^ "// end stmt "^ (Int.toString l) ^"."*)
  pp_stmti i s
  
fun pp_stmt s = pp_stmti "" s
fun pp_func name (Function(rtp,locals,formals,pre,body,post)) =
  pp_tp rtp ^ " " ^ name ^ "(" ^ (String.concatWith ", " (map (fn (s,tp) => pp_tp tp ^ " " ^ pp_sym s) formals)) ^ ")" ^
  "\nrequires:\n"^pp_annoi tab pre^
  "\nensures:\n"^pp_annoi tab post^
  "\n{\n" ^ pp_stmti tab body ^ "\n}"

structure Make = struct
  fun make_tp (t: Ast.tp) =
    case t of
      Ast.Int => Int
    | Ast.Bool => Bool
    | Ast.String => String
    | Ast.Char => Char
    | Ast.Pointer t' => Pointer (make_tp t')
    | Ast.Array t' => Array (make_tp t')
    | Ast.StructName sn => StructName sn
    | Ast.TypeName tn => make_tp (Syn.expand_def t)
    | Ast.Void => Void
    | Ast.Any => raise Fail "must resolve the type first"
  
  fun tp_of_field sn f =
    let fun find (Ast.Field(f',tp,_)::fields) f = (case Symbol.compare(f',f) of
                                                    EQUAL => tp
                                                 | _ => find fields f)
          | find [] f = raise Fail "field does not exist in struct"
    in case Structtab.lookup sn of
         SOME(Ast.Struct(s', SOME(fields), _, _)) => find fields f
       | _ => raise Fail "struct does not exist or not yet defined"
    end
  
  fun select_single (s,f) =
    case tp_of s of
       StructName sn => 
          let val t = make_tp (tp_of_field sn f) in
            case s of 
               Select(ptr, (sn', f'), _) => Select(ptr, (sn', f::f'), t)
             | Deref _ => Select(s, (sn,[f]), t)
             | _ => raise Fail ("ill-typed, not select of deref or select" ^ (pp_expr s))
          end
     | _ => raise Fail "ill-typed, field not selecting from struct type."
  fun select (p, f) =
    let fun efield_tp (sn,[]) = StructName sn
          | efield_tp (sn,f::fs) = 
              (case efield_tp (sn,fs) of 
                 StructName s => make_tp(tp_of_field s f))
    in Select(p, f, efield_tp f) end
  fun deref(p) = 
    case tp_of p of
       Pointer tp => Deref(p, tp)
     | _ => raise Fail "ill-typed, deref of non-pointer type"
  fun sub (a, i) = 
    case tp_of a of
       Array tp => Sub(a, i, tp)
     | _ => raise Fail "ill-typed, subscript of non-array type"
  (*fun cond(c, a, b) = 
  fun rel(oper, a, b) =*)
  fun I i = ValOp(IntConst (Word32.fromInt i),[])
  
  local
    fun stmts_list s = 
      case s of 
         Seq ss => List.concat (map stmts_list ss)
       | _ => [s]
  in
    fun sseq s =
      case s of 
         Seq ss => 
          (case stmts_list(Seq(map sseq ss)) of 
              [s] => s
            | ss => Seq ss)
       | If (g,a,b)=> 
           let val (a,b) = (sseq a, sseq b)
           in if isNop a andalso isNop b then Seq[]
              else If(g, a, b) end
       | While (gs, g, Anno (i1,i2,i3), b) => 
            While(sseq gs, g, Anno (sseq i1, sseq i2, sseq i3), sseq b)
       | Block (i,s) => Block(i, sseq s)
       | Assume _ => s
       | Assert _ => s
       | Check (Anno(a,b,c)) => Check(Anno(sseq a, sseq b, sseq c))
       | Assign _ => s
       | Break i => s
       | Comment _ => s
       | LabeledS (l, Seq[]) => Seq[] (* Remove labeled nop's *)
       | LabeledS (l, s) => LabeledS(l, sseq s)
    fun sblock s = 
      let val empty = IntListSet.empty
          val single = IntListSet.singleton
          val merge = foldl IntListSet.union IntListSet.empty
          fun without s i = IntListSet.difference (s, single i)
      in
        case s of 
           Seq ss => 
              let val (free, stmts) = ListPair.unzip (map sblock ss)
              in (merge free, Seq stmts) end
         | If (g,a,b)=> 
             let val ((fa,a'),(fb,b')) = (sblock a, sblock b)
             in (merge [fa,fb], If(g, a, b)) end
             
         | While (gs, g, is, b) => 
             let val ((fgs,gs'),(fb,b')) = (sblock gs, sblock b)
             in (merge[fgs,fb], While(gs', g, is, b')) end
         | Block (i,s) => 
              let val (free, s') = sblock s
              in case IntListSet.member(free, i) of
                    true => (without free i, Block(i, s'))
                  | false => (without free i, s')
              end
         | Assume _ => (empty, s)
         | Assert _ => (empty, s)
         | Check (Anno(a,b,c)) => (empty, s)
         | Assign _ => (empty, s)
         | Break i => (single i, s)
         | Comment _ => (empty, s)
         | LabeledS(l,s) => 
             let val (f,s') = sblock s
             in (f, LabeledS(l, s')) end
      end
    val simplify = #2 o sblock o sseq
  end
end

end
