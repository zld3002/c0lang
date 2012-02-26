(* The basic grammar of the C0 language - expressions, statements, and programs *)
(* Robert J. Simmons, Jakob Uecker  *)

structure C0 = struct
  type pc = int

  (* Different from the spec, since we may need to introduce temporary ids *)
  datatype ident = Normal of string | Temp of string * int 

  (**********************)
  (*** C0 expressions ***)
  (**********************)

  datatype constant 
    = Bool of bool       (* true or false           *)
    | Int of Word32.word (* 1, -241, 1523, 0xBEEF   *)
    | Char of char       (* '5', 'c', '\n', '\t'    *)
    | String of string   (* "Hello World"           *)
    | NullPointer        (* NULL                    *)

  type variable_name 
    = ident              (* x, y, z                 *)

  type function_name 
    = string             (* main, f, g, h, print    *)

  type type_name
    = string             (* node, t, file           *)

  type field_name
    = string             (* f, x, y                 *)

  datatype monop 
    = LogicNot           (* !e                      *)
    | ArithNeg           (* -e                      *)
    | BitNot             (* ~e                      *)

  datatype binop 
    = (* Arith      + * - / %    *) Plus | Times | Minus | Div | Mod
    | (* Bitwise    & | ^        *) BitAnd | BitOr | BitXor
    | (* Boolean    && ||        *) LogicAnd | LogicOr
    | (* Shift      << >>        *) ShiftLeft | ShiftRight 
    | (* Comparison < <= == >= > *) Lt | Leq | Eq | Geq | Gt | Neq

  type assignop 
    = binop option       (* =, +=, *=, -=, /=, %=, &=, |=, ^=, &&= ...       *)

  datatype postop 
    = Inc                                             (* lhs++               *) 
    | Dec                                             (* lhs--               *)

  type struct_decl = type_name                        (* struct t            *)

  datatype ty 
    = TyUnit                                          (* void                *)
    | TyVar of type_name                              (* t                   *)
    | TyBool                                          (* bool                *)
    | TyInt                                           (* int                 *)
    | TyString                                        (* string              *)
    | TyChar                                          (* char                *)
    | TyPointer of ty                                 (* ty*                 *)
    | TyArray of ty                                   (* ty[]                *)
    | TyStruct of struct_decl                         (* struct t            *)

  fun ty_string ty = 
    case ty of
      TyUnit => "void"
    | TyVar s => "(type variable " ^ s ^ ")"
    | TyBool => "bool"
    | TyInt => "int"
    | TyString => "string"
    | TyChar => "char"
    | TyPointer ty => ty_string ty ^ " *"
    | TyArray ty => ty_string ty ^ " []"
    | TyStruct s => "struct " ^ s

  datatype exp  
    = Const of constant                               (* 4, 12, "Hello"      *)
    | Var of variable_name                            (* x                   *)
    | Binop of exp * binop * exp                      (* e + e, e && e, ...  *)
    | Ref of exp                                      (* *e                  *)
    | Monop of monop * exp                            (* !e, ~e, -e          *)
    | Index of exp * exp                              (* e[e0]               *)
    | Call of call_expression                         (* e(e1,...,en)        *)
    | RefField of exp * field_name                    (* e->f                *)
    | Field of exp * field_name                       (* e.f                 *)
    | Ternary of exp * exp * exp                      (* e ? et : ef         *)
    | Alloc of ty                                     (* alloc(ty)           *)
    | AllocArray of ty * exp                          (* allocarray(ty,e)    *)

  and call_expression
    = Func of exp * exp list * pc                     (* e(e1,...,en)        *)

  and lhs 
    = LHSVar of variable_name                         (* x                   *)
    | LHSRef of lhs                                   (* *lhs                *)
    | LHSIndex of lhs * exp                           (* lhs[e]              *)
    | LHSRefField of lhs * field_name                 (* lhs->f              *)
    | LHSField of lhs * field_name                    (* lhs.f               *)

  (*********************)
  (*** C0 statements ***)
  (*********************)

  datatype simple_statement
    = Assign of exp * assignop * exp * pc             (* e = e0              *)
    | SimpleCall of call_expression                   (* e(e1,...,en)        *)
    | Postop of exp * postop * pc                     (* e++, e--            *)
    | Noop                                            (* ;;                  *)

  datatype statement
    = Decl of ty * variable_name * exp option * pc    (* ty x [ = e ]        *) 
    | Simple of simple_statement                      (* e=e0, e++, ...      *)
    | Return of exp option * pc                       (* return [ e ];       *)
    | Break of pc                                     (* break;              *)
    | Continue of pc                                  (* continue;           *)
    | If of exp * pc * statement * statement option   (* if(e) s [else s]    *)
    | While of exp * pc * statement                   (* while(e) s          *)
    | For of simple_statement                         (* for([s];[e];[s])s   *)
             * (exp * pc) option                      
             * simple_statement 
             * statement
    | Compound of statement list                      (* { s1 ... sn }       *)

  (*******************)
  (*** C0 programs ***)
  (*******************)

  type struct_def 
    = struct_decl * (ty * field_name) list            (* struct t {ty f,...} *)

  type function_decl
    = ty * function_name * (ty * variable_name) list  (* ty f (ty x, ...)    *)

  datatype decl 
    = DeclStructDecl of struct_decl                   (* struct t            *)
    | DeclStructDef of struct_def                     (* struct t { ... }    *)
    | DeclTypeDefTy of ty * type_name                 (* typedef ty t        *)
    | DeclExternFun of function_decl                  (* extern ty f(...)    *)
    | DeclFunDecl of function_decl                    (* ty f(...);          *)
    | DeclFunDef of function_decl * statement list    (* ty f(...) { ... }   *)

  type program = decl list

  (* Given a way to dereference type variables, removes them. *)
  fun find_ty (f : string -> ty) ty = 
    case ty of
      TyVar t => find_ty f (f t)
    | TyPointer ty => TyPointer (find_ty f ty)
    | TyArray ty => TyArray (find_ty f ty)
    | ty => ty

end

structure MapX =
RedBlackMapFn(struct type ord_key = C0.ident
              val compare = 
                  fn (C0.Normal x, C0.Normal y) => String.compare(x,y)
                   | (C0.Normal x, C0.Temp _) => GREATER
                   | (C0.Temp _, C0.Normal y) => LESS
                   | (C0.Temp (s1,x), C0.Temp (s2,y)) => 
                     (case Int.compare(x,y) of
                        EQUAL => String.compare (s1,s2) | ord => ord) 
              end)
