(* VAST is AST with one change made: Variables can carry a version number *)
signature VAST =
sig
  type ident = Ast.ident
  type tp = Ast.tp
  type oper = Ast.oper

  type ext = Mark.ext option

  (* Expressions *)
  datatype exp =
      (* SVar is the most important change made. It allows for version numbers. *)
      SVar of ident * int 		  (* x_i *)
    | IntConst of Word32.word	  (* n, -2^31 <= n < 2^31 *)
    | StringConst of string       (* "..." *)
    | CharConst of char		  (* 'c' *)
    | True			  (* true *)
    | False			  (* false *)
    | Null			  (* NULL *)
    | OpExp of oper * exp list	  (* oper(e1,...,en) *)
    | Select of exp * ident       (* e.f or e->f *)
    | FunCall of ident * exp list (* g(e1,...,en) *)
    | AddrOf of ident             (* &g *)
    | Invoke of exp * exp list    (* (e)(e1,...,en) *)
    | Alloc of tp		  (* alloc(tp) *)
    | AllocArray of tp * exp	  (* alloc_array(tp,e) *)
    | Cast of tp * exp            (* (tp)e *)
    | Result			  (* \result, in @ensures *)
    | Length of exp		  (* \length(e), in contracts *)
    | Hastag of tp * exp          (* \hastype(tp,e), in contracts *)
    | Marked of exp Mark.marked	  (* mark with source region info *)


  (* Variable declarations
  and vardecl =			    (* tp x; or tp x = e; *)
      VarDecl of ident * int * tp * exp option * ext *)
  (* reserve Ast.VarDecl for types *)
  (* define something new called SVarDecl for Function decl. *)
  (* need to define a new global Function decl. as well *)
  (* leave Ast.tp unchanged*)
  datatype svardecl =
      SVarDecl of ident * int * tp * exp option * ext

  (* Statements *)
  datatype stm =
      Assign of oper option * exp * exp     (* lv = e; or lv op= e; *)
    | Exp of exp			    (* e; *)
    | Seq of stm list	    (* { stms } *)
    | StmDecl of svardecl		    (* d *)
    | If of exp * stm * stm		    (* if (e) s1 else s2 *)
    | While of exp * spec list * stm            (* while (e) s, loop invs. *)
    | For of stm * exp * stm * spec list * stm  (* for (s1; e; s2) s3, loop invs. *)
    | Continue				    (* continue; *)
    | Break				    (* break; *)
    | Return of exp option		    (* return [e]; *)
    | Assert of exp * exp list              (* assert(e); error msgs *)
    | Error of exp                          (* error(e); *)
    | Anno of spec list		            (* @assert or @loop_invariant *)
    | Markeds of stm Mark.marked            (* mark with source region info *)


    (* Specs (for contracts) *)
  and spec =
      Requires of exp * ext	 (* @requires *)
    | Ensures of exp * ext	 (* @ensures *)
    | LoopInvariant of exp * ext (* @loop_invariant *)
    | Assertion of exp * ext	 (* @assert *)



  datatype basicblock = Block of ident * tp * svardecl list * stm * spec list 
                      | Empty
  (* Programs
  type prog = gdecl list *)

  
  (* print abstract syntax, with redundant parentheses *)
  structure Print :
  sig
    val ppSvar : ident * int -> string
    val ppExp : exp -> string
    val ppStm : stm -> string
    val ppBlock : basicblock -> string
    val ppSpec : spec -> string
    (* val pp_program : program -> string *)
  end

end

structure VAst :> VAST =
struct
  (* Printing C0 source, with redundant parentheses
   * and some syntactic sugar expanded *)
 
      type ident = Ast.ident
      type tp = Ast.tp
      type oper = Ast.oper

      type ext = Mark.ext option

      (* Expressions *)
      datatype exp =
          (* SVar is the most important change made. It allows for version numbers. *)
          SVar of ident * int 		  (* x_i *)
        | IntConst of Word32.word	  (* n, -2^31 <= n < 2^31 *)
        | StringConst of string       (* "..." *)
        | CharConst of char		  (* 'c' *)
        | True			  (* true *)
        | False			  (* false *)
        | Null			  (* NULL *)
        | OpExp of oper * exp list	  (* oper(e1,...,en) *)
        | Select of exp * ident       (* e.f or e->f *)
        | FunCall of ident * exp list (* g(e1,...,en) *)
        | AddrOf of ident             (* &g *)
        | Invoke of exp * exp list    (* (e)(e1,...,en) *)
        | Alloc of tp		  (* alloc(tp) *)
        | AllocArray of tp * exp	  (* alloc_array(tp,e) *)
        | Cast of tp * exp            (* (tp)e *)
        | Result			  (* \result, in @ensures *)
        | Length of exp		  (* \length(e), in contracts *)
        | Hastag of tp * exp          (* \hastype(tp,e), in contracts *)
        | Marked of exp Mark.marked	  (* mark with source region info *)
      (* Variable declarations
      and vardecl =			    (* tp x; or tp x = e; *)
          VarDecl of ident * int * tp * exp option * ext *)
      (* reserve Ast.VarDecl for types *)
      (* define something new called SVarDecl for Function decl. *)
      (* need to define a new global Function decl. as well *)
      (* leave Ast.tp unchanged*)
      datatype svardecl =
          SVarDecl of ident * int * tp * exp option * ext

      (* Statements *)
      datatype stm =
          Assign of oper option * exp * exp     (* lv = e; or lv op= e; *)
        | Exp of exp			    (* e; *)
        | Seq of stm list	    (* { stms } *)
        | StmDecl of svardecl		    (* d *)
        | If of exp * stm * stm		    (* if (e) s1 else s2 *)
        | While of exp * spec list * stm            (* while (e) s, loop invs. *)
        | For of stm * exp * stm * spec list * stm  (* for (s1; e; s2) s3, loop invs. *)
        | Continue				    (* continue; *)
        | Break				    (* break; *)
        | Return of exp option		    (* return [e]; *)
        | Assert of exp * exp list              (* assert(e); error msgs *)
        | Error of exp                          (* error(e); *)
        | Anno of spec list		            (* @assert or @loop_invariant *)
        | Markeds of stm Mark.marked            (* mark with source region info *)


    (* Specs (for contracts) *)
    and spec =
        Requires of exp * ext	 (* @requires *)
      | Ensures of exp * ext	 (* @ensures *)
      | LoopInvariant of exp * ext (* @loop_invariant *)
      | Assertion of exp * ext	 (* @assert *)
  


    (* Fields of structs *)
    (* datatype field =
        Field of ident * tp * ext	tp f; *)
    datatype basicblock = Block of ident * tp * svardecl list * stm * spec list 
                        | Empty

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

      fun ppSvar (sym, i) = 
          (Symbol.name sym) ^ "/" ^ (Int.toString i)
      
      fun ppExp e = 
          case e of
            SVar (sym, i) => ppSvar (sym, i)
          | IntConst n => "0x" ^ (Word32.toString n)
          | StringConst s => "\"" ^ s ^ "\""
          | CharConst c => "'" ^ (Char.toString c) ^ "'"
          | True => "true"
          | False => "false"
          | Null => "NULL"
          | OpExp (Ast.SUB, [e1, e2]) => (ppExp e1) ^ "[" ^ (ppExp e2) ^ "]"
          | OpExp (Ast.COND, [e1, e2, e3]) => (ppExp e1) ^ " ? " ^ (ppExp e2) ^ " : " ^ (ppExp e3)
          | OpExp (oper, [e1]) => (Ast.Print.pp_oper oper) ^ "(" ^ (ppExp e1) ^ ")"
          | OpExp (oper, [e1, e2]) => "(" ^ (ppExp e1) ^ ")" ^ (Ast.Print.pp_oper oper) ^ "(" ^ (ppExp e2) ^ ")"
          | OpExp (oper, el) => "(" ^ (Ast.Print.pp_oper oper) ^ "(" ^ (commas ", " (map ppExp el)) ^ ")"
          | Select (e1, f) => "(" ^ (ppExp e1) ^ ")." ^ (Symbol.name f)
          | FunCall (f, el) => (Symbol.name f) ^ "(" ^ (commas ", " (map ppExp el)) ^ ")"
          | Result => "\\result"
          | AddrOf g => "&" ^ (Symbol.name g)
          | Invoke (e0, el) => "(" ^ (ppExp e0) ^ ")(" ^ (commas ", " (map ppExp el)) ^ ")"
          | Alloc tp => "alloc(" ^ (Ast.Print.pp_tp tp) ^ ")"
          | AllocArray (tp, e0) => "alloc_array(" ^ (Ast.Print.pp_tp tp) ^ "," ^ (ppExp e0) ^ ")"
          | Cast (tp, e0) => "(" ^ (Ast.Print.pp_tp tp) ^ ")" ^ (ppExp e0)
          | Length e0 => "\\length(" ^ (ppExp e0) ^ ")"
          | Hastag (tp, e0) => "\\hastype(" ^ (Ast.Print.pp_tp tp) ^ "," ^ (ppExp e0) ^ ")"
          | Marked x => ppExp (Mark.data x)

      fun ppSpec spec =
            case spec of
                Requires (e0, ext) => "//@requires " ^ (ppExp e0)
              | Ensures (e0, ext) => "//@ensures " ^ (ppExp e0)
              | LoopInvariant (e0, ext) => "//@loop_invariant " ^ (ppExp e0)
              | Assertion (e0, ext) => "//@assert " ^ (ppExp e0)
      
      fun ppStm (stm : stm) : string =
          case stm of
              Assign (SOME (oper), e1, e2) => (ppExp e1) ^ " " ^ (Ast.Print.pp_oper oper) ^ "= " ^ (ppExp e2)
            | Assign (NONE, e1, e2) => (ppExp e1) ^ " = " ^ (ppExp e2)
            | Exp e0 => (ppExp e0) ^ ";"
            | Seq sl => commas ";\n" (map ppStm sl)
            | StmDecl (SVarDecl (sym, i, tp, e0, ext)) => 
               (case e0 of 
                    NONE => (ppSvar (sym, i)) ^ " : " ^ (Ast.Print.pp_tp tp)
                  | SOME e0' => (ppSvar (sym, i)) ^ " : " ^ (Ast.Print.pp_tp tp) ^ " = " ^ (ppExp e0'))
            | If (e0, s1, s2) => "if (" ^ (ppExp e0) ^ ") " ^ (ppStm s1) ^ " else " ^ (ppStm s2)
            | While (e0, sl, s) => "while (" ^ (ppExp e0) ^ ") " ^ (ppStm s)
            | For (s0, e0, s1, sl, s) => "for (" ^ (ppStm s0) ^ "; " ^ (ppExp e0) ^ "; " ^ (ppStm s1) ^ ") " ^ (ppStm s)
            | Continue => "continue"
            | Break => "break"
            | Return (SOME e0) => "return " ^ (ppExp e0)
            | Return (NONE) => "return"
            | Assert (e0, el) => "assert(" ^ (ppExp e0) ^ ")" ^ (newlines "; " (map ppExp el))
            | Error (e0) => "error(" ^ (ppExp e0) ^ ")"
            | Anno (sl) => "{" ^ (newlines "; " (map ppSpec sl)) ^ "}"
            | Markeds (s0) => ppStm (Mark.data s0)

          fun ppArgs svardecls =
              commas ", " (map (fn (SVarDecl (sym, i, tp, e0, ext)) => (ppSvar (sym, i)) ^ " : " ^ (Ast.Print.pp_tp tp)) svardecls)
          fun ppBlock block =
              case block of
                  Block (sym, tp, svardecls, body, specs) => 
                       Ast.Print.pp_tp tp ^ " " ^ (Symbol.name sym) ^ "(" ^ (ppArgs svardecls) ^ ")\n" ^
		                   (newlines "\n" (map ppSpec specs)) ^
                       "{\n" ^
                       ppStm body ^
                       "\n}"
                | Empty => "EmptyBasicBlock"
    end

end
