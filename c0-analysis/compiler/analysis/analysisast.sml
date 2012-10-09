(* C0 Compiler
 * Analysis Abstract Syntax Tree
 * Jason Koenig <jrkoenig@andrew.cmu.edu>
 *)
signature LOCAL_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol * int
signature SYM_MAP = ORD_MAP where type Key.ord_key = Symbol.symbol

structure LocalMap :> LOCAL_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol * int
             val compare = (fn ((v,i), (v',i')) => 
                                case Symbol.compare (v,v') of
                                   EQUAL => Int.compare(i,i')
                                 | r => r)
      end)
structure SymMap :> SYM_MAP = RedBlackMapFn (
      struct type ord_key = Symbol.symbol val compare = Symbol.compare end)


signature VERIFICATIONERROR =
sig 
   type error
   val VerificationError : (Mark.ext option * string) -> error
   val Wrap: string * error list -> error list
   val pp_error : error -> string
end

structure VError :> VERIFICATIONERROR =
struct
   datatype err = VE of Mark.ext option * string
   type error = err
   fun VerificationError x = VE x
   fun Wrap (s, l) =
     map (fn VE(e, s') => VE(e,s ^ s')) l
   fun pp_error (VE (SOME e, s)) =
                    "error at " ^ (Mark.show e) ^ ": " ^ s
     | pp_error (VE (NONE, s)) =
                    "error: " ^ s
end

signature AAST = 
sig
   
   exception UnsupportedConstruct of string
   
   type tp = Ast.tp
   type symbol = Symbol.symbol
   type loc = Symbol.symbol * int
   datatype aexpr = 
       Local of loc
     | Op of Ast.oper * (aexpr list)
     | Call of Symbol.symbol * (aexpr list)
     | IntConst of Word32.word
     | BoolConst of bool
     | StringConst of string
     | CharConst of char
     | Alloc of tp
     | Null
     | Result
     | Length of aexpr
     | Old of aexpr
     | AllocArray of tp * aexpr
     | Select of aexpr * symbol
     | MarkedE of aexpr Mark.marked
   datatype aphi = 
       PhiDef of (Symbol.symbol * int * (int list))
   datatype astmt = 
       Nop
     | Seq of astmt * astmt
     | Assert of aexpr (* assert(e); *)
     | Annotation of aexpr (* //@assert e; *)
     | Def of aexpr * aexpr (* Local (v,i) = e *)
     | Assign of aexpr * (Ast.oper option) * aexpr
     | Expr of aexpr
     | Break
     | Continue
     | PhiBlock of (aphi list)
     | Return of aexpr option
     | If of aexpr * astmt * astmt
     | While of (aphi list) * aexpr * (aexpr list) * astmt
     | MarkedS of astmt Mark.marked
   datatype afunc =
       Function of tp * (tp SymMap.map) * ((Ast.ident * tp * loc) list) * (aexpr list) * astmt * (aexpr list)
       (*return type, type map, formals, requires, body, ensures *)
   structure Print :
	  sig
		 val pp_aphi : aphi -> string
		 val pp_aexpr : aexpr -> string
		 val pp_astmt : astmt -> string
		 val pp_afunc : afunc -> string
		 val commas : string -> string list -> string
	  end
end

structure AAst :> AAST = 
struct
   
   exception UnsupportedConstruct of string
   
   type symbol = Symbol.symbol
   type tp = Ast.tp
   type loc = Symbol.symbol * int
   datatype aexpr = 
       Local of loc
     | Op of Ast.oper * (aexpr list)
     | Call of Symbol.symbol * (aexpr list)
     | IntConst of Word32.word
     | BoolConst of bool
     | StringConst of string
     | CharConst of char
     | Alloc of Ast.tp
     | Null
     | Result
     | Length of aexpr
     | Old of aexpr
     | AllocArray of Ast.tp * aexpr
     | Select of aexpr * symbol
     | MarkedE of aexpr Mark.marked
   datatype aphi = 
       PhiDef of (Symbol.symbol * int * (int list))
   datatype astmt = 
       Nop
     | Seq of astmt * astmt
     | Assert of aexpr (* assert(e); *)
     | Annotation of aexpr (* //@assert e; *)
     | Def of aexpr * aexpr (* Local (v,i) = e *)
     | Assign of aexpr * (Ast.oper option) * aexpr
     | Expr of aexpr
     | Break
     | Continue
     | PhiBlock of (aphi list)
     | Return of aexpr option
     | If of aexpr * astmt * astmt
     | While of (aphi list) * aexpr * (aexpr list) * astmt
     | MarkedS of astmt Mark.marked
   datatype afunc =
       Function of tp * (tp SymMap.map) * ((Ast.ident * tp * loc) list) * (aexpr list) * astmt * (aexpr list)
       (*return type, formals, requires, body, ensures *)
   structure Print =
   struct
      (*
        creates a string with c interleaved between elements of sl, in one string*)
		fun commas c sl = case sl of
		                     [] => ""
		                  |  x::[] => x
		                  |  x::xs => x ^ c ^ (commas c xs)
		
		fun pp_aphi (PhiDef(sym, i, l)) = 
		    (Symbol.name sym)^"`"^(Int.toString i) ^
		       ":=phi("^(commas ", " 
		                 (map (fn j => (Symbol.name sym)^"`"^(Int.toString j)) l))
		                 ^")"
		       
		fun pp_aexpr (Local (sym, i)) =
		      (Symbol.name sym) ^ "`" ^ (Int.toString i)
		  | pp_aexpr (Op(Ast.SUB, [e1,e2])) =
			   pp_aexpr e1 ^ "[" ^ pp_aexpr e2 ^ "]"
		  | pp_aexpr (Op(Ast.COND, [e1,e2,e3])) =
		      (pp_aexpr e1 ^ " ? " ^ pp_aexpr e2 ^ " : " ^ pp_aexpr e3)
		  | pp_aexpr (Op (oper, [e])) = 
		       (Ast.Print.pp_oper oper) ^"(" ^ pp_aexpr e ^ ")"
		  | pp_aexpr (Op (oper, [e1, e2])) = 
		       "(" ^ pp_aexpr e1 ^ " " ^(Ast.Print.pp_oper oper) ^" "^ pp_aexpr e2 ^ ")"
		  | pp_aexpr (Op (oper, l)) = 
		       "(" ^ (Ast.Print.pp_oper oper) ^ ")"^
		           "(" ^ (commas ", " (map pp_aexpr l)) ^ ")"
		  | pp_aexpr (IntConst w) = "0x"^(Word32.toString w)
		  | pp_aexpr (BoolConst b) = if b then "true" else "false"
		  | pp_aexpr (StringConst s) = "\"" ^ s ^ "\"" (* TODO: escape properly *)
		  | pp_aexpr (CharConst c) = "'" ^ Char.toString c ^ "'" (* TODO: escape properly *)
		  | pp_aexpr (Call (sym, l)) =
		       (Symbol.name sym) ^ "(" ^ (commas ", " (map pp_aexpr l)) ^ ")"
		  | pp_aexpr (Null) = "NULL"
      | pp_aexpr (Result) = "\\result"
      | pp_aexpr (Length(e)) = "\\length(" ^ pp_aexpr(e) ^ ")"
      | pp_aexpr (Old(e)) = "\\old(" ^ pp_aexpr(e) ^ ")"
		  | pp_aexpr (Alloc (tp)) =
		       "alloc("^(Ast.Print.pp_tp tp)^")"
		  | pp_aexpr (AllocArray (tp, e)) =
		       "alloc("^(Ast.Print.pp_tp tp)^","^(pp_aexpr e)^")"
		  | pp_aexpr (Select (e, f)) =
		       "(" ^ (pp_aexpr e) ^ ")."^(Symbol.name f)
		  | pp_aexpr (MarkedE me) = pp_aexpr (Mark.data me)

		fun pp_astmt (Nop) = "(void)"
		  | pp_astmt (Seq(s, s')) = (pp_astmt s) ^ ";\n" ^ (pp_astmt s')
		  | pp_astmt (Assert(e)) = "assert(" ^ (pp_aexpr e) ^ ")"
		  | pp_astmt (Annotation(e)) = "/*@assert(" ^ (pp_aexpr e) ^ ")*/"
		  | pp_astmt (Def(lv, e)) = (pp_aexpr lv) ^ " := " ^ (pp_aexpr e)
		  | pp_astmt (Assign(lv, oper, e)) = 
		        (pp_aexpr lv) ^ " "^
		          (case oper of NONE => "" | SOME oper' => Ast.Print.pp_oper oper')
		         ^"= " ^ (pp_aexpr e)
		  | pp_astmt (Expr(e)) = (pp_aexpr e)
		  | pp_astmt (PhiBlock(p)) = commas ";\n" (map pp_aphi p)
		  | pp_astmt (Break) = "break"
		  | pp_astmt (Continue) = "continue"
		  | pp_astmt (Return (NONE)) = "return"
		  | pp_astmt (Return (SOME e)) = "return " ^(pp_aexpr e)
		  | pp_astmt (If (e, s1, s2)) = "if (" ^(pp_aexpr e) ^ ") {\n"
		                                   ^(pp_astmt s1) ^ "\n} else {\n"
		                                   ^ (pp_astmt s2) ^ "\n}" 
		  | pp_astmt (While (p, e, specs, stm)) = 
		     "while\n"^
		      (commas ";\n" (map pp_aphi p))
		      ^"\n" ^(commas ";\n" (map (fn s => "//@loop_invariant" ^ (pp_aexpr s)) specs))
		      ^"\n(" ^ (pp_aexpr e) ^") {\n"
		          ^ (pp_astmt stm) ^ "\n}"
		  | pp_astmt (MarkedS ms) = pp_astmt (Mark.data ms)
		
		fun pp_afunc (Function (rtp, map, formals, requires, body, ensures))=
		  pp_astmt body
		end
end
