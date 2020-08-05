(* Checks for unreachable code.
 * Example:
 * int foo(int x) {
 *   if (x > 3) {
 *     // ....
 *     return ...;
 *   }
 *   else { 
 *     // ....
 *     return ...;
 *   }
 * 
 *   // This line should produce a warning
 *   println("This is unreachable");
 * }

 * Ishan Bhargava (ibhargav@andrew)
 *)
structure WarnUnreachable : sig 
  (* Prints out all unreachable code *)
  val warn_program: Ast.program -> unit
end = struct
  fun flip f x y = f y x 
  (* Function to use when showing a warning *)
  (* warn_func : string -> Ast.ext -> unit *)
  val warn_func = flip ErrorMsg.warn 
  (* Once -Werror is implemented *)
  (* val warn_func = flip ErrorMsg.error *)

  fun warn stmnt = let 
    (* Gets the position of a vardecl list, by 
     * using the position of the first decl. *)
    val get_decls_pos = fn 
        [] => NONE 
      | (Ast.VarDecl (_, _, _, pos))::_ => pos

    (* Gets the source position information associated with the statement.
     * If no source information could be found, then it returns default *)
    fun get_pos default = fn 
        Ast.Markeds m => Mark.ext m 
      | Ast.Seq (decls, _) => get_decls_pos decls 
      | _ => default

    (* warn_statement: Ast.ext -> Ast.stm -> (Ast.ext, bool)
     * Returns true if this statement always returns/halts *)
    val rec warn_statement = fn 
      Ast.Markeds m => warn_statement (Mark.data m)
    | Ast.Error _ => true (* error(...) always crashes the program *)
    | Ast.Continue => true
    | Ast.Break => true 
    | Ast.Return _ => true 
    | Ast.If (_, ifBody, elseBody) => 
        let val a = warn_statement ifBody
            val b = warn_statement elseBody 
        in a andalso b end 

    (* Loops always return false since we could skip them *)
    | Ast.For (_, _, _, _, body) => 
        let val _ = warn_statement body
        in false end 
    | Ast.While (_, _, body) => 
        let val _ = warn_statement body 
        in false end 

    | Ast.Seq (decls, list) => let 
        val initial_pos = get_decls_pos decls 

        (* If continue is false, then don't do anything (stop looping) 
         * If done is set, then anything which comes next should be warned about, 
         * and then after that we set continue to false *)
        val process_stm = fn (stm, data as (pos, done, continue)) => 
          case (continue, done) of 
            (true, true) => 
              let val () = warn_func "unreachable code" (get_pos pos stm) 
              in (NONE, true, false) end 
          | (true, false) => (get_pos pos stm, warn_statement stm, true)
          | _ => data 
        in #2 ((List.foldl process_stm (initial_pos, false, true)) list)
        end 
    (* Ignore other function calls *)
    | _ => false 

    in 
      if Flags.warning_enabled "unreachable-code" 
        then ignore (warn_statement stmnt)
        else () 
    end 

  fun warn_decl (d: Ast.gdecl) = case d of
    Ast.Function(_, _, _, SOME body, _, _, _) => warn body 
  | _ => () 

  fun warn_program gdecls = List.app warn_decl gdecls
end 