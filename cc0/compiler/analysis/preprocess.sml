
signature PREPROCESS =
sig
   exception UnsupportedConstruct of string
   (* defined only for functions. Removes parallel declarations, generates
      variable type table. Also, Seq is always Seq([], l), i.e. all vardecls
      are StmDecls. Also runs isolation if the first parameter is true. *)
   val preprocess : bool -> Ast.gdecl -> Ast.stm * (Ast.tp SymMap.map)
   val fold_stacked_defns : Ast.program -> Ast.program
end

structure Preprocess :> PREPROCESS = 
struct

   exception UnsupportedConstruct of string
   open Ast 
   
   fun preprocessArgs wL args = 
     let fun addDecl (VarDecl(i, tp, _,_), (init, remap, types)) =
        case SymSet.member(wL, i) of 
           true => 
              let val i' = Symbol.new (Symbol.name i)
                  val t = Syn.expand_all tp 
              in 
                ((StmDecl(VarDecl(i', tp, SOME (Var i), NONE)))::init,
                 SymMap.insert (remap, i, i'),
                 SymMap.insert(SymMap.insert(types, i, t), i', t))
              end
         | false => (init, SymMap.insert (remap, i, i), SymMap.insert(types, i, Syn.expand_all tp))
     in foldl addDecl ([], SymMap.empty, SymMap.empty) args end
   
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
       | Cast(t, e') => Cast(t, color mapping e')
       | Result => e
       | Length e' => Length(color mapping e')
       | Hastag(t, e') => Hastag(t, color mapping e')
       | Marked m => Marked(Mark.map (color mapping) m)
   
   fun specColor mapping s =
      case s of 
         Requires (e, ext) => Requires (color mapping e, ext)
       | Ensures (e, ext) => Ensures (color mapping e, ext)
       | LoopInvariant (e, ext) => LoopInvariant (color mapping e, ext)
       | Assertion (e, ext) => Assertion (color mapping e, ext)
       
   val empty = SymMap.empty
   fun merge m m' = SymMap.unionWith (#1) (m, m')
   
   
   fun writtenLocals stmt =
      case stmt of
         Assign (oper, Var x, e) => SymSet.singleton x
       | Assign (oper, Marked m, e) => 
          (case Mark.data m of 
              Var x => SymSet.singleton x
            | _ => SymSet.empty)
       | Assign (oper, _, e) => SymSet.empty
       | Exp e => SymSet.empty
       | Seq (vars, stmts) => 
           foldl SymSet.union SymSet.empty (map writtenLocals (stmts))
              (* ignore vars because shadowing is disallowed. *)
       | StmDecl (VarDecl(v, tp, e, ext)) => SymSet.empty
       | If (e, s1, s2) => 
           SymSet.union(writtenLocals s1, writtenLocals s2)
       | While (e, specs, s) => writtenLocals s
       | Continue => SymSet.empty
       | Break => SymSet.empty
       | Return _ => SymSet.empty
       | Assert _ => SymSet.empty
       | Error e => SymSet.empty
       | Anno annos => SymSet.empty
       | Markeds m => writtenLocals (Mark.data m)
       | For _ => raise UnsupportedConstruct "Bad construct"
       
   
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
       | Error e => 
           (Error (color mapping e), empty, mapping)
       | Anno annos => (Anno (map (specColor mapping) annos), empty, mapping)
       | Markeds m => 
           let val (s', mapping', types) = preprocess' (Mark.data m, mapping)
           in (Markeds (Mark.mark' (s', Mark.ext m)), mapping', types) end
       | For _ => raise UnsupportedConstruct "Bad construct"
       
   fun preprocess iso f =
     case f of
        Function(name, rtp, args, SOME stmt, specs, false, ext) =>
          let val wL = writtenLocals stmt
              val (init, remap, types) = preprocessArgs wL args
              val stmts = 
                 case iso of
                    true => Isolate.iso_stm (Symbol.digest 
                                                 (SymMap.listItemsi types))
                                            stmt 
                  | false => [stmt]
                 
              val (stmt', types', remap') = preprocess' (Seq([],stmts), remap)
              val stmt'' = case Syn.expand_def rtp of 
                              Void => Seq([],[stmt', Return NONE])
                            | _ => stmt'
              val stmt''' = Seq([], init @ [stmt'])
          in (stmt''',
              SymMap.map Syn.expand_all 
              (SymMap.unionWith (#1) (types, types')))
          end
      | _ => raise UnsupportedConstruct "Bad construct"
  
   (* TODO: this doesn't actually work, as the annotations that get checked depend
      on where the function is called from in the source. So only annotations
      that are present up to the point where the function is invoked should be actually
      used. *)
   fun fold_stacked_defns prog =
     let
      val (other, internal_fn) = List.partition
                                        (fn Ast.Function(_,_,_,_,_,extern,_) => extern | _ => true) prog
                 (* TODO: check that the sort used in AUtil.collect is stable. *)
      val funcs = AUtil.collect Symbol.compare
                         (map (fn f as (Ast.Function(n,_,_,_,_,_,_)) => (n,f)) internal_fn)
      fun getPreconditions (Ast.Function(_,_,_,_,specs,_,_)) = 
        List.mapPartial (fn s as (Ast.Requires _) => SOME s | _ => NONE) specs
      fun getPostconditions (Ast.Function(_,_,_,_,specs,_,_)) = 
        List.mapPartial (fn s as (Ast.Ensures _) => SOME s | _ => NONE) specs
      fun getBody (Ast.Function(_,_,_,body,_,_,ext)) = 
        case body of SOME b => [(b, ext)] | NONE => []
      fun foreach (n, fs as f_first::_) =
         let val pre  = List.concat (map getPreconditions (rev fs))
             val post = List.concat (map getPostconditions fs)
             val bodyext = List.concat (map getBody fs)
             val Ast.Function(name, rtp, form, _, specs, extern, ext) = f_first
             val body' = case bodyext of [] => NONE | [(b,e)] => SOME b
             
             val ext' = case bodyext of [] => ext | [(b,e)] => e
         in
             Ast.Function(name, rtp, form, body', pre @ post, extern, ext')
         end
    in other @ (map foreach funcs) end
end
