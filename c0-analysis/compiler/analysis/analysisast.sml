(* C0 Compiler
 * Analysis Abstract Syntax Tree
 * Jason Koenig <jrkoenig@andrew.cmu.edu>
 *)

signature AAST = 
sig
   type symbol = Symbol.symbol
   datatype aexpr = 
       Local of Symbol.symbol * int
     | Op of Ast.oper * (aexpr list)
     | Call of Symbol.symbol * (aexpr list)
     | IntConst of Word32.word
     | BoolConst of bool
     | Default
     | Alloc of Ast.tp
     | Null
     | AllocArray of Ast.tp * aexpr
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
   structure Print :
	  sig
		 val pp_aphi : aphi -> string
		 val pp_aexpr : aexpr -> string
		 val pp_astmt : astmt -> string
	  end
end

structure AAst :> AAST = 
struct
   type symbol = Symbol.symbol
   datatype aexpr = 
       Local of Symbol.symbol * int
     | Op of Ast.oper * (aexpr list)
     | Call of Symbol.symbol * (aexpr list)
     | IntConst of Word32.word
     | BoolConst of bool
     | Default
     | Alloc of Ast.tp
     | Null
     | AllocArray of Ast.tp * aexpr
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
   structure Print =
   struct
      (*commas string -> string list -> string
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
		  | pp_aexpr (Default) = "<default>"
		  | pp_aexpr (Call (sym, l)) =
		       (Symbol.name sym) ^ "(" ^ (commas ", " (map pp_aexpr l)) ^ ")"
		  | pp_aexpr (Null) = "NULL"
		  | pp_aexpr (Alloc (tp)) =
		       "alloc("^(Ast.Print.pp_tp tp)^")"
		  | pp_aexpr (AllocArray (tp, e)) =
		       "alloc("^(Ast.Print.pp_tp tp)^","^(pp_aexpr e)^")"

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
		
		end
end
