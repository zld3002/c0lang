
signature PREPROCESS =
sig
   exception UnsupportedConstruct of string
   (* defined only for functions. Removes parallel declarations, generates
      variable type table. Also, Seq is always Seq([], l), i.e. all vardecls
      are StmDecls. *)
   val preprocess : Ast.gdecl -> Ast.stm * (Ast.tp SymMap.map)
end

structure Preprocess :> PREPROCESS = 
struct

   exception UnsupportedConstruct of string
   open Ast 
   
   fun preprocessArgs args = 
     let fun addDecl (VarDecl(i, tp, _,_), (remap, types)) =
        (SymMap.insert (remap, i, i), SymMap.insert(types, i, tp))
     in foldl addDecl (SymMap.empty, SymMap.empty) args end
   
   fun color mapping e =
      case e of  
         Var x =>
           (case SymMap.find (mapping, x) of
               SOME x' => Var x'
             | NONE => raise Fail "variable not in scope?")
       | IntConst _ => e
       | StringConst _ => e
       | CharConst _ => e
       | True => e
       | False => e
       | Null => e
       | OpExp (oper, el) => OpExp(oper, map (color mapping) el)
       | Select (e', f) => Select (color mapping e', f)
       | FunCall (f, el) => FunCall(f, map (color mapping) el)
       | Alloc _ => e
       | AllocArray (t, e') => AllocArray(t, color mapping e')
       | Result => e
       | Length e' => Length(color mapping e')
       | Old e' => Old(color mapping e')
       | Marked m => Marked(Mark.map (color mapping) m)
   
   fun specColor mapping s =
      case s of 
         Requires (e, ext) => Requires (color mapping e, ext)
       | Ensures (e, ext) => Ensures (color mapping e, ext)
       | LoopInvariant (e, ext) => LoopInvariant (color mapping e, ext)
       | Assertion (e, ext) => Assertion (color mapping e, ext)
       
   val empty = SymMap.empty
   fun merge m m' = SymMap.unionWith (fn (a,b) => a) (m, m')
   
   fun preprocess' (stmt, mapping) =
      case stmt of
         Assign (oper, lv, e) =>
               (Assign(oper, color mapping lv, color mapping e), empty, mapping)
       | Exp e => (Exp(color mapping e), empty, mapping)
       | Seq ([], stmts) =>
           let fun f (stmt, (stmts, t, m)) = 
                  let val (stmt', t', m') = preprocess' (stmt, m)
                  in (stmt' :: stmts, merge t t', m') end
               val s = ([], empty, mapping)
               val (stmts', types', mapping') = foldl f s stmts
           in (Seq([], List.rev stmts'), types', mapping') end
       | Seq (vars, stmts) => 
           let val vars' = map (fn v => StmDecl v) vars
           in preprocess' (Seq([], vars' @ stmts), mapping) end
       | StmDecl (VarDecl(v, tp, e, ext)) =>
           let val v' = Symbol.new (Symbol.name v)
           in
            (StmDecl (VarDecl(v', tp, Option.map (color mapping) e, ext)),
             SymMap.insert(empty, v', tp),
             SymMap.insert (mapping, v, v'))
           end
       | If (e, s1, s2) => 
           let val (s1', types1, mapping1) = preprocess' (s1, mapping)
               val (s2', types2, mapping1) = preprocess' (s2, mapping)
           in
             (If(color mapping e, s1', s2'), merge types1 types2, mapping)
           end
       | While (e, specs, s) =>
           let val (s', types, mapping') = preprocess' (s, mapping)
           in
             (While(color mapping e, map (specColor mapping) specs, s'),
              types, mapping)
           end
       | Continue	=> (Continue, empty, mapping)
       | Break	=> (Break, empty, mapping)
       | Return (SOME e) => (Return (SOME (color mapping e)), empty, mapping)
       | Return (NONE) => (Return (NONE), empty, mapping)
       | Assert (e, errs) =>
           (Assert (color mapping e, map (color mapping) errs), empty, mapping)
       | Anno annos => (Anno (map (specColor mapping) annos), empty, mapping)
       | Markeds m => 
           let val (s', mapping', types) = preprocess' (Mark.data m, mapping)
           in (Markeds (Mark.mark' (s', Mark.ext m)), mapping', types) end
       | For _ => raise UnsupportedConstruct "Bad construct"
       
   fun preprocess f =
     case f of
        Function(name, rtp, args, SOME stmt, specs, false, ext) =>
          let val (remap, types) = preprocessArgs args
              val stmts = 
                 Isolate.iso_stm (Symbol.digest (SymMap.listItemsi types))
                                 stmt
              val (stmt', types', remap') = preprocess' (Seq([],stmts), remap)
          in (stmt',
              SymMap.map Syn.expand_all 
              (SymMap.unionWith (#1) (types, types')))
          end
      | _ => raise UnsupportedConstruct "Bad construct"
end
