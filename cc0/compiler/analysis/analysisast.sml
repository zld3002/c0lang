(* C0 Compiler
 * Analysis Abstract Syntax Tree
 * Jason Koenig <jrkoenig@andrew.cmu.edu>
 *)

signature AAST = 
sig
   
   exception UnsupportedConstruct of string
   
   type tp = Ast.tp
   type symbol = Symbol.symbol
   type loc = Symbol.symbol * int
   type field = symbol * symbol
   datatype aexpr = 
       Local of loc
     | Op of Ast.oper * (aexpr list)
     | Call of Symbol.symbol * (aexpr list)
     | AddrOf of Symbol.symbol
     | Invoke of aexpr * aexpr list
     | IntConst of Word32.word
     | BoolConst of bool
     | StringConst of string
     | CharConst of char
     | Alloc of tp
     | Null
     | Result
     | Length of aexpr
     | Hastag of tp * aexpr
     | AllocArray of tp * aexpr
     | Cast of tp * aexpr
     | Select of aexpr * symbol * symbol
     | MarkedE of aexpr Mark.marked
   datatype aphi = 
       PhiDef of (Symbol.symbol * int * (int list))
   datatype modifies = ModFields of field list | ModAnything
   
   datatype astmt = 
       Nop
     | Seq of astmt * astmt
     | Assert of aexpr (* assert(e); *)
     | Error of aexpr (* error(e); *)
     | Annotation of aexpr (* //@assert e; *)
     | Def of loc * aexpr (* Local (v,i) = e *)
     | Assign of aexpr * (Ast.oper option) * aexpr
     | Expr of aexpr
     | Break
     | Continue
     | Return of aexpr option
     | If of aexpr * astmt * astmt * (aphi list)
     | While of (aphi list) * aexpr * (aexpr list) * modifies * astmt * (aphi list)
     | MarkedS of astmt Mark.marked
   datatype afunc =
       Function of tp * symbol * (tp SymMap.map) * ((Ast.ident * tp * loc) list) * (aexpr list) * astmt * (aexpr list)
       (*return type, name, type map, formals, requires, body, ensures *)
       
   type aprog = afunc list
   
   val lookup : aprog -> symbol -> afunc
   
   structure Print :
	  sig
	   val pp_loc : loc -> string
		 val pp_aphi : aphi -> string
		 val pp_aexpr : aexpr -> string
		 val pp_verif_aexpr : aexpr -> string
		 val pp_astmt : astmt -> string
		 val pp_afunc : afunc -> string
		 val pp_aprog : aprog -> string
		 val commas : string -> string list -> string
	  end
end

structure AAst :> AAST = 
struct
   
   exception UnsupportedConstruct of string
   
   type symbol = Symbol.symbol
   type tp = Ast.tp
   type loc = Symbol.symbol * int
   type field = symbol * symbol
   datatype aexpr = 
       Local of loc
     | Op of Ast.oper * (aexpr list)
     | Call of Symbol.symbol * (aexpr list)
     | AddrOf of Symbol.symbol
     | Invoke of aexpr * aexpr list
     | IntConst of Word32.word
     | BoolConst of bool
     | StringConst of string
     | CharConst of char
     | Alloc of Ast.tp
     | Null
     | Result
     | Length of aexpr
     | Hastag of tp * aexpr
     | AllocArray of Ast.tp * aexpr
     | Cast of tp * aexpr
     | Select of aexpr * symbol * symbol
     | MarkedE of aexpr Mark.marked
   datatype aphi = 
       PhiDef of (Symbol.symbol * int * (int list))
   datatype modifies = ModFields of field list | ModAnything
   
   datatype astmt = 
       Nop
     | Seq of astmt * astmt
     | Assert of aexpr (* assert(e); *)
     | Error of aexpr (* error(e); *)
     | Annotation of aexpr (* //@assert e; *)
     | Def of loc * aexpr (* Local (v,i) = e *)
     | Assign of aexpr * (Ast.oper option) * aexpr
     | Expr of aexpr
     | Break
     | Continue
     | Return of aexpr option
     | If of aexpr * astmt * astmt * (aphi list)
     | While of (aphi list) * aexpr * (aexpr list) * modifies * astmt * (aphi list)
     | MarkedS of astmt Mark.marked
   datatype afunc =
       Function of tp * symbol * (tp SymMap.map) * ((Ast.ident * tp * loc) list) * (aexpr list) * astmt * (aexpr list)
       (*return type, formals, requires, body, ensures *)
   
   type aprog = afunc list
   
   fun lookup [] _ = raise Fail "Function does not have an analyzed form"
     | lookup ((desc as Function(_,n,_,_,_,_,_))::rest) f =
            if Symbol.compare(f,n) = EQUAL then desc else lookup rest f
   structure Print =
   struct
      (*
        creates a string with c interleaved between elements of sl, in one string*)
		fun commas c sl = case sl of
		                     [] => ""
		                  |  x::[] => x
		                  |  x::xs => x ^ c ^ (commas c xs)
		fun newlines c sl = case sl of
		                     [] => ""
		                  |  x::[] => x ^ c
		                  |  x::xs => x ^ c ^ (newlines c xs)
		
		fun pp_aphi (PhiDef(sym, i, l)) = 
		    (Symbol.name sym)^"`"^(Int.toString i) ^
		       ":=phi("^(commas ", " 
		                 (map (fn j => (Symbol.name sym)^"`"^(Int.toString j)) l))
		                 ^")"
		fun pp_loc (sym, i) = 
		      (Symbol.name sym) ^ "`" ^ (Int.toString i)

		fun pp_aexpr (Local l) = pp_loc l
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
          | pp_aexpr (Hastag(tp, e)) = "\\hastag(" ^ Ast.Print.pp_tp tp ^ "," ^ pp_aexpr(e) ^ ")"
		  | pp_aexpr (Alloc (tp)) =
		       "alloc("^(Ast.Print.pp_tp tp)^")"
		  | pp_aexpr (AllocArray (tp, e)) =
		       "alloc("^(Ast.Print.pp_tp tp)^","^(pp_aexpr e)^")"
                  | pp_aexpr (Cast(tp, e)) =
                       "cast(" ^ Ast.Print.pp_tp tp ^ "," ^ pp_aexpr e ^ ")"
		  | pp_aexpr (Select (e, s, f)) =
		       "(" ^ (pp_aexpr e) ^ ")."^(Symbol.name f)
		  | pp_aexpr (MarkedE me) = pp_aexpr (Mark.data me)

		fun pp_verif_aexpr (Local l) = pp_loc l
		  | pp_verif_aexpr (Op(Ast.SUB, [e1,e2])) =
			   pp_verif_aexpr e1 ^ "[" ^ pp_verif_aexpr e2 ^ "]"
		  | pp_verif_aexpr (Op(Ast.COND, [e1,e2,e3])) =
		      (pp_verif_aexpr e1 ^ " ? " ^ pp_verif_aexpr e2 ^ " : " ^ pp_verif_aexpr e3)
		  | pp_verif_aexpr (Op (oper, [e])) = 
		       (Ast.Print.pp_oper oper) ^"(" ^ pp_verif_aexpr e ^ ")"
		  | pp_verif_aexpr (Op (oper, [e1, e2])) = 
		       "(" ^ pp_verif_aexpr e1 ^ " " ^(Ast.Print.pp_oper oper) ^" "^ pp_verif_aexpr e2 ^ ")"
		  | pp_verif_aexpr (Op (oper, l)) = 
		       "(" ^ (Ast.Print.pp_oper oper) ^ ")"^
		           "(" ^ (commas ", " (map pp_verif_aexpr l)) ^ ")"
		  | pp_verif_aexpr (IntConst w) = LargeInt.toString (Word32.toLargeIntX w)
		  | pp_verif_aexpr (BoolConst b) = if b then "true" else "false"
		  | pp_verif_aexpr (StringConst s) = "\"" ^ s ^ "\"" (* TODO: escape properly *)
		  | pp_verif_aexpr (CharConst c) = "'" ^ Char.toString c ^ "'" (* TODO: escape properly *)
		  | pp_verif_aexpr (Call (sym, l)) =
		       (Symbol.name sym) ^ "(" ^ (commas ", " (map pp_verif_aexpr l)) ^ ")"
		  | pp_verif_aexpr (Null) = "NULL"
          | pp_verif_aexpr (Result) = "\\result"
          | pp_verif_aexpr (Length(e)) = "\\length(" ^ pp_verif_aexpr(e) ^ ")"
          | pp_verif_aexpr (Hastag(tp, e)) = "\\hastag(" ^ Ast.Print.pp_tp tp ^ "," ^ pp_verif_aexpr(e) ^ ")"
		  | pp_verif_aexpr (Alloc (tp)) =
		       "alloc("^(Ast.Print.pp_tp tp)^")"
		  | pp_verif_aexpr (AllocArray (tp, e)) =
		       "alloc("^(Ast.Print.pp_tp tp)^","^(pp_verif_aexpr e)^")"
                  | pp_verif_aexpr (Cast (tp, e)) =
                       "cast(" ^ Ast.Print.pp_tp tp ^ "," ^ pp_verif_aexpr e ^ ")"
		  | pp_verif_aexpr (Select (e, s, f)) =
		       "(" ^ (pp_verif_aexpr e) ^ ")."^(Symbol.name f)
		  | pp_verif_aexpr (MarkedE me) = pp_verif_aexpr (Mark.data me)

    fun pp_mod ModAnything = "*"
      | pp_mod (ModFields fs) = commas ", " (map (fn (s,f) => Symbol.name s ^"."^ Symbol.name f) fs)
		fun pp_astmt (Nop) = "(void)"
		  | pp_astmt (Seq(s, s')) = (pp_astmt s) ^ ";\n" ^ (pp_astmt s')
		  | pp_astmt (Assert(e)) = "assert(" ^ (pp_aexpr e) ^ ")"
		  | pp_astmt (Error(e)) = "error(" ^ (pp_aexpr e) ^ ")"
		  | pp_astmt (Annotation(e)) = "/*@assert(" ^ (pp_aexpr e) ^ ")*/"
		  | pp_astmt (Def((sym,i), e)) = (Symbol.name sym) ^ "`" ^ 
		        (Int.toString i) ^ " := " ^ (pp_aexpr e)
		  | pp_astmt (Assign(lv, oper, e)) = 
		        (pp_aexpr lv) ^ " "^
		          (case oper of NONE => "" | SOME oper' => Ast.Print.pp_oper oper')
		         ^"= " ^ (pp_aexpr e)
		  | pp_astmt (Expr(e)) = (pp_aexpr e)
		  | pp_astmt (Break) = "break"
		  | pp_astmt (Continue) = "continue"
		  | pp_astmt (Return (NONE)) = "return"
		  | pp_astmt (Return (SOME e)) = "return " ^(pp_aexpr e)
		  | pp_astmt (If (e, s1, s2, phis)) = "if (" ^(pp_aexpr e) ^ ") {\n"
		                                   ^(pp_astmt s1) ^ "\n} else {\n"
		                                   ^ (pp_astmt s2) ^ "\n}"
		                                   ^ (commas ";\n" (map pp_aphi phis))
		  | pp_astmt (While (p1, e, specs, modif, stm, p2)) = 
		     "while\n"^
		      (commas ";\n" (map pp_aphi p1))
		      ^"\n" ^(commas ";\n" (map (fn s => "//@loop_invariant" ^ (pp_aexpr s)) specs))
		      ^"\n//@modifies " ^ (pp_mod modif) ^ ";"
		      ^"\n(" ^ (pp_aexpr e) ^") {\n"
		          ^ (pp_astmt stm) ^ "\n}" ^ (commas ";\n" (map pp_aphi p2))
		  | pp_astmt (MarkedS ms) = pp_astmt (Mark.data ms)
		
		fun pp_afunc (Function (rtp, name, tp_map, formals, requires, body, ensures))=
		  Ast.Print.pp_tp rtp ^ " " ^ (Symbol.name name) ^ "(...)\n" ^
		  (newlines "\n" (map (fn req => "//@requires " ^ pp_aexpr req ^ ";") requires)) ^
		  (newlines "\n" (map (fn ens => "//@ensures " ^ pp_aexpr ens ^ ";") ensures)) ^
		  "{\n" ^
		  pp_astmt body ^
		  "\n}"
		
		fun pp_aprog funcs = newlines "\n" (map pp_afunc funcs)
		end
end
