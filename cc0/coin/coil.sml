(* C0 Interpreter
 * C0il - C0 Intermediate language
 * Robert J. Simmons, Jakob Uecker *)

structure C0Internal = struct

(**********************)
(*** C0 expressions ***)
(**********************)
datatype idtype = Actual of string | Temporary of string 
type id = Symbol.symbol (* * idtype *)

datatype const = 
   Bool of bool                             (* true or false               *)
 | Int of Word32.word                       (* 1, -241, 1523, 0xBEEF       *)
 | Char of char                             (* '5', 'c', '\n', '\t'        *)
 | String of string                         (* "Hello World"               *)
 | NullPointer                              (* NULL                        *)

datatype monop =
   LogicNot                                 (* !e                          *)
 | ArithNeg                                 (* -e                          *)
 | BitNot                                   (* ~e                          *)

datatype binop = 
   (* Arith      + * - / %    *) Plus | Times | Minus | Div | Mod
 | (* Bitwise    & | ^        *) BitAnd | BitOr | BitXor
 | (* Shift      << >>        *) ShiftLeft | ShiftRight 
 | (* Comparison < <= == >= > *) Lt | Leq | Eq | Geq | Gt | Neq | Addr

type assignop = binop option (* =, +=, *=, -=, /=, %=, &=, |=, ^=, &&= ... *)

datatype exp = 
   Const of const                           (* 4, 12, "Hello"              *)
 | Var of id                                (* x                           *)
 | LogicOr of exp * exp                     (* e || e                      *)
 | LogicAnd of exp * exp                    (* e && e                      *)
 | Binop of exp * binop * exp               (* e + e, e && e, ...          *)
 | Ref of exp                               (* *e                          *)
 | Monop of monop * exp                     (* !e, ~e, -e                  *)
 | Index of exp * exp                       (* e[e0]                       *)
 | Field of exp * id                        (* e.foo                       *)
 | Call of id * exp list * Mark.ext         (* foo(e1,...,en)              *)
 | Ternary of exp * exp * exp               (* e ? et : ef                 *)
 | Alloc of Ast.tp                          (* alloc(ty)                   *)
 | AllocArray of Ast.tp * exp               (* allocarray(ty,e)            *)
 | Length of exp                            (* \length(e)                  *)

(********************************)
(*** C0 Intermediate Language ***)
(********************************)

type label = int 
datatype cmd = 
   Label of label * string
 | Exp of exp * Mark.ext
 | Declare of Ast.tp * id * (exp * Mark.ext) option
 | Assign of binop option * exp * exp * Mark.ext
 | CCall of id option * id * exp list * Mark.ext 
 | Assert of exp * string * Mark.ext
 | CondJump of exp * Mark.ext * label
 | Jump of label
 | Return of (exp * Mark.ext) option

 (* Manipulating the scope *)
 | PushScope
 | PopScope of int

type program = cmd vector * int vector

local
   fun lp b = if b then "(" else ""
   fun rp b = if b then ")" else ""
in

fun constToString (c: const): string = 
   case c of
      Bool true => "true"
    | Bool false => "false"
    | Int i => Word32Signed.toString i
    | Char c => "'" ^ Char.toCString c ^ "'"
    | String s => "\"" ^ String.translate Char.toCString s ^ "\""
    | NullPointer => "NULL"

fun binopToString (oper: binop): string = 
   case oper of Plus => "+" | Times => "*" | Minus => "-" | Div => "/" 
     | Mod => "%" | BitAnd => "&" | BitOr => "|" | BitXor => "^"
     | ShiftLeft => "<<" | ShiftRight => ">>" | Lt => "<" | Leq => "<=" 
     | Eq => "==" | Geq => ">=" | Gt => ">" | Neq => "!=" | Addr => "*"

fun monopToString (oper: monop): string = 
   case oper of LogicNot => "!" | ArithNeg => "-" | BitNot => "~"

(* expToString b exp - the b determines whether enclosing parens are needed *)
fun expToString (b: bool) (exp: exp) = 
   case exp of 
      Const c => constToString c
    | Var x => Symbol.name x
    | LogicOr (e1, e2) => 
      lp b ^ expToString true e1 ^ " || " ^ expToString true e2 ^ rp b
    | LogicAnd (e1, e2) => 
      lp b ^ expToString true e1 ^ " && " ^ expToString true e2 ^ rp b
    | Binop (e1, oper, e2) => lp b ^ expToString true e1 ^ " " 
      ^ binopToString oper ^ " " ^ expToString true e2 ^ rp b
    | Ref e1 => lp b ^ "*" ^ expToString true e1 ^ rp b
    | Monop (oper, e1) => lp b ^ monopToString oper ^ expToString true e1 ^ rp b
    | Index (e1, e2) => expToString true e1 ^ "[" ^ expToString false e2 ^ "]"
    | Field (Ref e1, f) => expToString true e1 ^ "->" ^ Symbol.name f
    | Field (e1, f) => expToString true e1 ^ "." ^ Symbol.name f
    | Call (f, es, pos) => Symbol.name f ^ "(" 
      ^ String.concatWith "," (map (expToString false) es) ^ ")"
    | Ternary (e, e1, e2) => lp b ^ expToString true e ^ " ? " 
      ^ expToString true e1 ^ " : " ^ expToString true e2 ^ rp b
    | Alloc ty => "alloc(" ^ Ast.Print.pp_tp ty ^ ")"
    | AllocArray (ty, e1) => "alloc_array(" ^ Ast.Print.pp_tp ty ^ ", " 
      ^ expToString false e1 ^ ")"
    | Length e1 => "\\length(" ^ expToString false e1 ^ ")"

fun cmdToString (cmd: cmd): string = 
   case cmd of
      Label (l, "") => "Label: L" ^ Int.toString l 
    | Label (l, s) => "Label: L" ^ Int.toString l ^ " // " ^ s
    | Exp (e1, pos) => (* Mark.show pos ^ "\n" ^ *) 
      expToString false e1
    | Declare (ty, x, NONE) => 
      "New " ^ Ast.Print.pp_tp ty ^ " " ^ Symbol.name x
    | Declare (ty, x, SOME (e, pos)) => 
      "New " ^ Ast.Print.pp_tp ty ^ " " ^ Symbol.name x
      ^ " = " ^ expToString false e
    | Assign (oper, e1, e2, pos) => (* Mark.show pos ^ "\n" ^ *) 
      expToString false e1 ^ " " 
      ^ (case oper of NONE => "" | SOME oper => binopToString oper) ^ "= "
      ^ expToString false e2
    (* | Call _ => "CALL" *)
    | Assert (e1, msg, pos) => (* Mark.show pos ^ "\n" ^ *) 
      "Assert " ^ expToString false e1 ^ " \"" ^ msg ^ "\""
    | CondJump (e1, pos, l) => (* Mark.show pos ^ "\n" ^ *) 
      "Go to L" ^ Int.toString l ^ " if not " ^ expToString false e1
    | Jump l => 
      "Go to L" ^ Int.toString l ^ ""
    | Return NONE => (* Mark.show pos ^ "\n" ^ *) 
      "Return"
    | Return (SOME (e1, pos)) => (* Mark.show pos ^ "\n" ^ *) 
      "Return " ^ expToString false e1
    | PushScope => "{"
    | PopScope n => String.concat (List.tabulate (n, (fn _ => "}")))
    | CCall(NONE,f,args,pos) => expToString false (Call(f,args,pos))
    | CCall(SOME(x),f,args,pos) => cmdToString (Assign(NONE,Var x,Call(f,args,pos),pos))

(* cmdPrint prefix prog - the prefix determines the indentation *)
fun cmdPrint (prefix: string) (prog : program): unit = 
   Vector.appi 
       (fn (i, cmd) =>
           print (prefix ^ Int.toString i ^ " - " ^ cmdToString cmd ^ "\n")) 
       (#1 prog)

end
end
