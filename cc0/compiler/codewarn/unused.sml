(* Warns about unused variables and also unused expressions
 * Ishan Bhargava 2020 (ibhargav@andrew) *)
structure WarnUnused = struct 
  (* The SML starter kit *)
  infixr $
  fun f $ x = f x
  
  infix |>
  fun x |> f = f x 

  fun flip f x y = f y x 
  fun when cond f = if cond then f () else () 

  (* List.foldl but with curried function *)
  fun foldl' f z = fn 
      [] => z 
    | x::xs => foldl' f (f x z) xs 

  val rec is_function = fn 
    Ast.FunCall _ => true
  | Ast.Invoke _ => true 
  | Ast.Marked m => is_function $ Mark.data m 
  | _ => false 

  (* could be used to track unused functions/structs/etc *)
  (* datatype symboltype = Variable | Function | Struct | Typedef  *)

  structure TrackedSymbolMap : sig 
    type entry = string * bool * Ast.ext
    type map 

    val empty : map 
    
    val mark_used : string -> map -> map 
    (* returns last position of that variable. unused for now *)
    val mark_unused : string * Ast.ext -> map -> Ast.ext option * map
    val add : string -> Ast.ext -> map -> map 
    (* Gets all symbol locations marked as unused from the current level of the
     * context stack *)
    val get_unused : map -> Ast.ext list 

    (* throws if no prior calls to push *)
    val pop : map -> map 
    val push : map -> map 

  end = struct 
    type entry = string * bool * Ast.ext 

    (* An associative list of symbol names, whether they were used,
     * and their declaration position. We also have a parent map for scopes *)
    datatype map = TSMap of entry list * map option

    val empty: map = TSMap ([], NONE)

    (* Marks symbol `name` as used. Searches up the parent
     * tree if necessary. Requires that `name` was previously
     * added to the table *)
    fun mark_used (name: string): map -> map = fn 
        TSMap ([], NONE) => raise Fail $ "INTERNAL ERROR: symbol '" ^ name ^ "' not in table"
      | TSMap ([], SOME parent) => TSMap ([], SOME (mark_used name parent))
      | TSMap ((id, status, pos)::xs, parent) => 
          if id = name 
            then TSMap ((id, true, pos)::xs, parent)
            else let val (TSMap (y, parent')) = mark_used name (TSMap (xs, parent))
                 in TSMap ((id, status, pos)::y, parent') end
    
    (* Updates symbol `name` to be unused with the new position.
     * Returns the old position. Requires that `name` was previously
     * added to the table *)
    fun mark_unused (name: string, new_pos: Ast.ext): map -> (Ast.ext option * map) = fn 
        TSMap ([], NONE) => raise Fail $ "INTERNAL ERROR: symbol '" ^ name ^ "' not in table"
      | TSMap ([], SOME parent) => 
          let val (data, parent') = mark_unused (name, new_pos) parent 
          in (data, TSMap ([], SOME parent')) end 

      | TSMap ((id, seen, pos)::xs, parent) => 
          if id = name 
            then (if not seen then SOME pos else NONE, TSMap ((id, false, new_pos)::xs, parent))
            else 
              let val (data, TSMap (y, parent')) = mark_unused (name, new_pos) (TSMap (xs, parent))
              in (data, TSMap ((id, seen, pos)::y, parent')) end

    fun add name pos (TSMap (map, parent)) = TSMap ((name, false, pos)::map, parent)

    fun get_unused (TSMap (map, parent)) = 
      List.map (fn (_, _, pos) => pos) o List.filter (fn (_, seen, _) => not seen) $ map 

    fun pop (TSMap (_, SOME parent)) = parent 
      | pop t = raise Fail "INTERNAL ERROR: popping from toplevel context!" 

    fun push t = TSMap ([], SOME t)
  end 

  (* Function to use when showing a warning *)
  (* warn_func : string -> Ast.ext -> unit *)
  val warn_func = flip ErrorMsg.warn 
  (* Once -Werror is implemented *)
  (* val warn_func = flip ErrorMsg.error *)

  val rec variable_name = fn 
      Ast.Var i => SOME (Symbol.name i, NONE)
    | Ast.Marked m => (
        case Mark.data m of 
            Ast.Var i => SOME (Symbol.name i, Mark.ext m)
          | other => variable_name other
        )
    | _ => NONE 

  (* Prints out all currently unused variables in table *)
  fun print_unused table = 
    when (Flags.warning_enabled "unused-variable") (fn () =>
      let 
        val unused: Ast.ext list = TrackedSymbolMap.get_unused table
      in 
        List.app (warn_func "value is never used") unused 
      end
    )

  fun warn_expression (e: Ast.exp) (data as (table, pos)): TrackedSymbolMap.map * Ast.ext = case e of 
      Ast.Marked marked_exp => warn_expression (Mark.data marked_exp) (table, Mark.ext marked_exp)
    | Ast.Var sym => (TrackedSymbolMap.mark_used (Symbol.name sym) table, pos)
    | Ast.AllocArray (_, count) => warn_expression count data
    | Ast.Select (v, _) => warn_expression v data
    | Ast.OpExp (_, exps) => foldl' warn_expression data exps 
    | Ast.FunCall (_, fArgs) => foldl' warn_expression data fArgs 
    | Ast.Invoke (fName, fArgs) => data |> 
        warn_expression fName |> flip (foldl' warn_expression) fArgs 
    | Ast.Cast (_, e) => warn_expression e data
    | Ast.Hastag (_, e) => warn_expression e data
    | Ast.Length e => warn_expression e data 
    | _ => data 

  fun warn_contract (c: Ast.spec) data = case c of 
    ((Ast.Requires (e, _)) | (Ast.Ensures (e, _)) | (Ast.Assertion (e, _)) | (Ast.LoopInvariant (e, _))) => 
      warn_expression e data 

  fun warn_contracts (c: Ast.spec list) data = foldl' warn_contract data c

  (* Takes in a variable declaration node and adds it to the given table
   * Returns the new table and also the position of the variable *)
  fun add_vardecl (Ast.VarDecl (vName, _, vExp, vPos), table): TrackedSymbolMap.map * Ast.ext = 
    let val table_with_var = TrackedSymbolMap.add (Symbol.name vName) vPos table
    in case vExp of 
         SOME e => warn_expression e (table_with_var, vPos)
       | NONE => (table_with_var, vPos)
    end 
    
  fun warn_statement (s: Ast.stm) (data as (table, pos)) : TrackedSymbolMap.map * Ast.ext = case s of 
      Ast.Markeds marked_statement => 
        warn_statement (Mark.data marked_statement) (table, Mark.ext marked_statement)
    | Ast.Exp e => (
      (* If this expression is a function call, then that's fine
       * Otherwise, it could be a typo *)
      when (not $ is_function e andalso Flags.warning_enabled "unused-expression") 
        (fn () => ErrorMsg.warn pos "expression result unused");
      (* Checks for unused variables *)
      warn_expression e data
    )
    (* We want to make sure a value is used after it is assigned to variable, so
     * if this is just a simple assignment like x = ..., then we mark x as unused
     * at this point  *)
    | Ast.Assign (_, lhs, rhs) => (
        case variable_name lhs of 
          SOME (name, pos) => 
            data |> warn_expression lhs |> warn_expression rhs
        | NONE => data |> warn_expression lhs |> warn_expression rhs
      )
        
    | Ast.Return (SOME e) => data |> warn_expression e 
    | Ast.StmDecl d => add_vardecl (d, table)
    | Ast.If (test, ifBody, elseBody) => data |>
        warn_expression test |> warn_statement ifBody |> warn_statement elseBody

    | Ast.While (test, contracts, body) => data |>
        warn_expression test |> warn_statement body 

    | Ast.For (init, test, next, contracts, body) => data |>
        warn_statement init |> 
        warn_expression test |> 
        warn_statement next |> 
        warn_statement body 
    | (Ast.Assert (e, _) | Ast.Error e) => (* second argument to Assert is error msgs which are compiler-generated *)
        warn_expression e data 
    | Ast.Anno cs => warn_contracts cs data 
    | Ast.Seq (decls: Ast.vardecl list, body: Ast.stm list) => (* new scope with new vars *)
        let 
          (* decls might come with expressions we need to check too *)
          val locals_table = List.foldl (#1 o add_vardecl) (TrackedSymbolMap.push table) decls 

          (* traverse body, updating the table as we go *)
          val (final_table, _) = foldl' warn_statement (locals_table, pos) body 
        in 
          print_unused final_table ; 
          (TrackedSymbolMap.pop final_table, pos)
        end 
    | _ => data

  and warn_decl (d: Ast.gdecl, table (* unused for now *)) = case d of
    Ast.Function(_, _, args, SOME body, contracts, _, _) => 
      (* Need a new table for the args *)
      let 
        val locals_table = (* Use an empty table because each function needs a new one *)
          List.foldl (#1 o add_vardecl) (TrackedSymbolMap.push table) args 

        val (finished_table: TrackedSymbolMap.map, _) = warn_statement body (locals_table, NONE) 
                                                     |> warn_contracts contracts
      in 
        print_unused finished_table ; 
        TrackedSymbolMap.pop finished_table
      end

  (* right now we only warn for unused local variables, could
   * be extended to deal with structs, functions, etc. *)
  | _ => table 

  (* Traverses each decl in the program *)
  and warn_program gdecls = ignore $ List.foldl warn_decl TrackedSymbolMap.empty gdecls
end
