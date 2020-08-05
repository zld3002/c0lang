structure ExpandPrintf :> sig 
  (* Expands printf(...) to print and printint,
   * and format(...) to string_join, string_fromint, etc. *)
  val expand_fdecl : Ast.gdecl -> Ast.gdecl
  val expand_stmnt : Ast.ext -> Ast.stm -> Ast.stm  
end = struct 
  infixr $
  fun f $ x = f x 

  (* SML implementation of the State monad *)

  (* Represents a computation which has a current
   * value and a current state
   * 'a: result type, 'b: state type *)
  type ('a, 'b) state = 'b -> 'a * 'b 

  (* Standard monad bind operation for State monad *)
  infix >>= =<< <$> 
  fun (f: ('a, 'c) state) >>= (g: 'a -> ('b, 'c) state) : ('b, 'c) state = 
    fn x => let val (x', s') = f x 
            in g x' s' end  

  (* Same thing but reversed *)
  fun g =<< f = f >>= g

  (* Basically lifting a regular function 
   * to apply it to the current value,
   * while not changing the state *)
  fun (f: 'a -> 'b) <$> (g: ('a, 'c) state) : ('b, 'c) state = 
    fn s => let val (x, s') = g s 
            in (f x, s') end 

  (* Executes state computation p 
   * with initial state s, giving back
   * only the final result *)
  fun execState (s: 'b) (p: ('a, 'b) state) : 'a = #1 (p s)

  (* Setting the computation's current value,
   * while not affecting the state *)
  fun return a = fn s => (a, s)

  (* Acessing the current value of the state *)
  val get = fn s => (s, s)

  (* op:: is not curried... *)
  fun cons x xs = x::xs 

  val pop: ('a option, 'a list) state = 
    fn x::xs => (SOME x, xs) 
     | []    => (NONE, [])

  datatype format_specifier = 
      PString (* %s *)
    | PInt (* %d *)
    | PChar (* %c *)
    | PLowerHex (* %x, not yet implemented (pending on moving int2hex to <string> instead of <util> *)
    | PUpperHex (* %X, not yet implemented *)
    | PNonFormatted of string 

  val char_to_format = fn 
    #"s" => PString 
  | #"d" => PInt 
  | #"c" => PChar 
  | #"%" => PNonFormatted "%"
  | #"x" => PLowerHex
  | #"X" => PUpperHex

  type 'a parser = ('a, char list) state 

  (* Reads characters up to a % and returns PNonFormatted s *)
  val munch_string: format_specifier parser = 
  let 
    (* We need a dummy parameter () because
     * of SML language limitations *) 
    fun munch_string' (): char list parser = 
      pop >>= (fn SOME #"%" => return [] 
                | NONE      => return [] 
                | SOME c    => cons c <$> munch_string' ())
  in 
    PNonFormatted o String.implode <$> munch_string' ()
  end 

  val munch_format: format_specifier parser = 
    char_to_format o Option.valOf <$> pop 

  fun split_format (s: string): format_specifier list = 
  let 
    fun split_format' (): format_specifier list parser = 
      munch_string >>= (fn str => get >>= (fn
          (* Stop if out of characters *)
          [] => return [str] 
          (* Otherwise munch_string stops at a %
           * so parse this format specifier and 
           * cons the two results *)
         | _ => munch_format >>= (fn fmt => 
                  cons str <$> (cons fmt <$> split_format' ()))))
  in 
    execState (String.explode s) (split_format' ())
  end 

  (* Replaces printf with a sequence of prints *)
  fun replace_printf ((fmt: string), (args: Ast.exp list)) (pos: Ast.ext) : Ast.stm = 
  let 
    val fmt_specifiers = split_format fmt 

    fun mk_funcall name args = (Ast.Exp (Ast.FunCall (Symbol.symbol name, args)))

    fun go (fmts: format_specifier list) (arg_exps: Ast.exp list) = case (fmts, arg_exps) of 
        (PNonFormatted s :: xs, ys) => mk_funcall "print" [Ast.StringConst s] :: go xs ys 
      | (PInt :: xs, y :: ys)       => mk_funcall "printint" [y] :: go xs ys 
      | (PChar :: xs, y :: ys)      => mk_funcall "printchar" [y] :: go xs ys 
      | (PString :: xs, y :: ys)    => mk_funcall "print" [y] :: go xs ys 
        (* TODO: Handle %x %X cases here and in format *)
      | _                           => [] 
  in
    Ast.Markeds $ Mark.mark' (Ast.Seq ([], go fmt_specifiers args), pos)
  end 

  fun replace_format ((fmt: string), (args: Ast.exp list)) (pos: Ast.ext) : Ast.exp = 
  let 
    val fmt_specifiers = split_format fmt 

    fun mk_funcall name args = Ast.FunCall (Symbol.symbol name, args)

    fun go (fmts: format_specifier list) (arg_exps: Ast.exp list) = case (fmts, arg_exps) of 
        (PNonFormatted s :: xs, ys) => Ast.StringConst s :: go xs ys 
      | (PInt :: xs, y :: ys)       => mk_funcall "string_fromint" [y] :: go xs ys 
      | (PChar :: xs, y :: ys)      => mk_funcall "string_fromchar" [y] :: go xs ys 
      | (PString :: xs, y :: ys)    => y :: go xs ys 
      | _                           => [] 

    fun join (x, y) = Ast.FunCall (Symbol.symbol "string_join", [x, y])
  in 
    Ast.Marked $ Mark.mark' (List.foldr join (Ast.StringConst "") (go fmt_specifiers args), pos)
  end 

  fun is_native s = 
    case Symtab.lookup s of 
      SOME (Ast.Function (_, _, _, _, _, is_extern, _)) => is_extern
    | _ => false 

  fun is_printf_like s = 
    case Symbol.name s of 
      "format" => is_native s
    | "printf" => is_native s
    | _ => false 

  (* If the given expression is a function,
   * returns a tuple containing its name
   * and args. Otherwise returns NONE  *)
  val rec get_function = fn
    Ast.Marked m => get_function $ Mark.data m 
  | Ast.FunCall f => SOME f 
  | _ => NONE 

  (* TODO: this can be condensed *)
  val get_fmt_and_args = fn 
    fmt_exp::args_exps => 
      let val (fmt_string, _) = 
          case fmt_exp of 
            Ast.StringConst s => (s, NONE)
          | Ast.Marked e => (
              case Mark.data e of 
                Ast.StringConst s => (s, Mark.ext e)
              | _ => raise Fail "printf expansion bug")
      in (fmt_string, args_exps) end 

  fun expand_exp (pos: Ast.ext) (e: Ast.exp): Ast.exp = case e of 
    Ast.Marked m => Ast.Marked $ Mark.map (expand_exp (Mark.ext m)) m 
  | Ast.FunCall (name, args) => if Symbol.name name = "format" andalso is_native name
                                  then replace_format (get_fmt_and_args (List.map (expand_exp pos) args)) pos 
                                  else Ast.FunCall (name, List.map (expand_exp pos) args)
  | Ast.OpExp (opr, exps) => Ast.OpExp (opr, List.map (expand_exp pos) exps)
  | Ast.Select (e, n) => Ast.Select (expand_exp pos e, n)
  | Ast.Invoke (e1, es) => Ast.Invoke (expand_exp pos e1, List.map (expand_exp pos) es)
  | Ast.AllocArray (t, e) => Ast.AllocArray (t, expand_exp pos e)
  | Ast.Cast (t, e) => Ast.Cast (t, expand_exp pos e)
  | Ast.Length e => Ast.Length (expand_exp pos e)
  | Ast.Hastag (t, e) => Ast.Hastag (t, expand_exp pos e)
  | _ => e 

  fun expand_vdecl (decl as Ast.VarDecl (name, tp, exp, pos)) =
    Ast.VarDecl (name, tp, Option.map (expand_exp pos) exp, pos)

  val expand_contract : Ast.spec -> Ast.spec = fn 
    Ast.Requires (e, pos) => Ast.Requires (expand_exp pos e, pos)
  | Ast.Ensures (e, pos) => Ast.Ensures (expand_exp pos e, pos)
  | Ast.Assertion (e, pos) => Ast.Assertion (expand_exp pos e, pos)
  | Ast.LoopInvariant (e, pos) => Ast.LoopInvariant (expand_exp pos e, pos)

  fun expand_stmnt (pos: Ast.ext) (s: Ast.stm): Ast.stm = case s of 
    Ast.Markeds m => Ast.Markeds $ Mark.map (expand_stmnt (Mark.ext m)) m 
  | Ast.Exp e => ( 
      case get_function e of 
        NONE => Ast.Exp $ expand_exp pos e
      | SOME (n, args) => if Symbol.name n = "printf" andalso is_native n
                            then replace_printf (get_fmt_and_args (List.map (expand_exp pos) args)) pos
                            else Ast.Exp $ expand_exp pos e)
                    
  | Ast.Seq (decls, body) => Ast.Seq (List.map expand_vdecl decls, List.map (expand_stmnt pos) body)
  | Ast.If (cond, ifBody, elseBody) => Ast.If (expand_exp pos cond, 
                                               expand_stmnt pos ifBody, 
                                               expand_stmnt pos elseBody)
  | Ast.While (test, contracts, body) => Ast.While (expand_exp pos test, 
                                                    List.map expand_contract contracts, 
                                                    expand_stmnt pos body)
  | Ast.For _ => raise Fail "for loops should be eliminated at this point" 
  | Ast.StmDecl vdecl => Ast.StmDecl $ expand_vdecl vdecl 
  | Ast.Assign (opr, lhs, rhs) => Ast.Assign (opr, lhs, expand_exp pos rhs)
  | Ast.Return (SOME v) => Ast.Return (SOME $ expand_exp pos v)
  | Ast.Assert (exp, msgs) => Ast.Assert (expand_exp pos exp, msgs)
  | _ => s 

  fun expand_fdecl (Ast.Function (name, rtp, params, SOME body, contracts, is_extern, pos)) = 
        Ast.Function (name, rtp, params, SOME $ expand_stmnt pos body, List.map expand_contract contracts, is_extern, pos)
    | expand_fdecl (other as Ast.Function (name, rtp, params, NONE, contracts, is_extern, pos)) = 
        Ast.Function (name, rtp, params, NONE, List.map expand_contract contracts, is_extern, pos)
end 