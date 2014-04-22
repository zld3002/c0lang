structure Modifies =
struct

    
  structure Pred = struct
    
    type ident = Gcl.ident
    type st = Gcl.ident
    type func = Gcl.ident
    type field = Gcl.field
    
    datatype predicate =
     (* Struct reachability *)
        FieldReach of st * st    (* Whether first struct reaches second via some field*)
      | Reach of st * st         (* Struct reaches b along some path*)
      | ReachSelf of st          (* Struct reaches self*)
      | ArgReaches of func * st  (* func has an argument reaching s*)
      | ModReaches of func * st  (* func can modify a struct based on reachablility*)
     (* Syntactic modification *)
      | ModifiesSource of func * field
      | IsField of st * field
      | Calls of func * func
      | Modifies of func * field
      | ModifiesInt of func * field
    
    open Syntax
      
    fun inj_s s = SCONST(Symbol.name s)
    val inj_fun = inj_s
    fun inj_fld (s,f) = SCONST((Symbol.name s) ^ "." ^ String.concatWith "." (map Symbol.name (rev f)))
    
    fun inj p =
      case p of
        FieldReach(s,s')  => P("FieldReach",[inj_s s, inj_s s'])
      | ReachSelf(s)      => P("ReachSelf",[inj_s s])
      | Reach(s,s')       => P("Reach",[inj_s s, inj_s s'])
      | ArgReaches(f,s)   => P("ArgReaches", [inj_fun f, inj_s s])
      | ModReaches(f,s)   => P("ModReaches", [inj_fun f, inj_s s])
      
      | ModifiesSource(f,sf) => P("ModifiesSource", [inj_fun f, inj_fld sf])
      | IsField(s,sf)        => P("IsField", [inj_s s, inj_fld sf])
      | Calls(f,g)           => P("Calls", [inj_fun f, inj_fun g])
      | Modifies(f, sf)      => P("Modifies", [inj_fun f, inj_fld sf])
      | ModifiesInt(f, sf)   => P("ModifiesInt", [inj_fun f, inj_fld sf])
    
    fun prj_s (SCONST s) = Symbol.symbol s
    val prj_fun = prj_s
    fun prj_fld (SCONST sf) = 
      let val s::fs = String.tokens (fn x => x = #".") sf
      in (Symbol.symbol s, rev(map Symbol.symbol fs)) end
    
    fun prj p =
      case p of  
        P("FieldReach",[s, s']) => FieldReach(prj_s s, prj_s s')
      | P("ReachSelf", [s]) => ReachSelf(prj_s s)
      | P("Reach", [s, s']) => Reach(prj_s s, prj_s s')
      | P("ArgReaches", [f, s]) => ArgReaches(prj_fun f, prj_s s)
      | P("ModReaches", [f, s]) => ModReaches(prj_fun f, prj_s s)
      
      | P("ModifiesSource", [f, sf]) => ModifiesSource(prj_fun f, prj_fld sf)
      | P("IsField", [s, sf]) => IsField(prj_s s, prj_fld sf)
      | P("Calls", [f, g]) => Calls(prj_fun f, prj_fun g)         
      | P("Modifies", [f, sf]) => Modifies(prj_fun f, prj_fld sf)
      | P("ModifiesInt", [f, sf]) => ModifiesInt(prj_fun f, prj_fld sf)
  end 
  
  structure Db = Bulp(Pred)
  
  datatype modifies = ModField of Gcl.field
                    | ModAnyField  (* Modify any field *)
                    | ModVar of Gcl.ident
                    | ModUnion of modifies list
  
  fun struct_reach_from_tp tp =
    case Syn.expand_def tp of
      Ast.Int => NONE
    | Ast.Bool => NONE
    | Ast.String => NONE
    | Ast.Char => NONE
    | Ast.Pointer tp => struct_reach_from_tp tp
    | Ast.Array tp => struct_reach_from_tp tp
    | Ast.StructName ident => SOME ident
    | Ast.TypeName _ => raise Fail "unreachable"
    | Ast.Void => NONE
    | Ast.Any => NONE
  
  (*TODO: Fix structure name*)
  structure IntSymMap = RedBlackMapFn(PairOrd(structure A = SymOrd structure B = IntOrd))
  
  val func_modifies = ref (SymMap.empty: modifies SymMap.map)
  val while_modifies = ref (IntSymMap.empty: modifies IntSymMap.map)
  fun bind_func (f, modclause) = 
    func_modifies := SymMap.insert(!func_modifies, f, modclause)
  fun bind_while (f, l, modclause) = 
    while_modifies := IntSymMap.insert(!while_modifies, (f,l), modclause)
  fun lookup f = 
    valOf(SymMap.find (!func_modifies, f))
  fun lookup_while (f,l) = 
    valOf(IntSymMap.find (!while_modifies, (f,l)))
  
  
  
  local val lookup_modifies = lookup
        open Gcl
  in
  fun vars_written s = 
    case s of 
      Assign (Local v, _) => [v]
    | Assign (_, _) => []
    | Seq s => List.concat (map vars_written s)
    | If (_,a,b) => (vars_written a) @ (vars_written b)
    | While (gs,g,inv,b) => (vars_written gs) @ (vars_written b)
    | Break _ => []
    | Block (_,s)=> vars_written s
    | Assert _ => []
    | Check _ => []
    | Assume _ => []
    | Comment _ => []
    | LabeledS (_,s) => vars_written s
  
  fun fields_written s = 
    case s of 
      Assign (Field(p,f), _) => [f]
    | Assign (_, _) => []
    | Seq s => List.concat (map fields_written s)
    | If (_,a,b) => (fields_written a) @ (fields_written b)
    | While (gs,g,inv,b) => (fields_written gs) @ (fields_written b)
    | Break _ => []
    | Block (_,s)=> fields_written s
    | Assert _ => []
    | Check _ => []
    | Assume _ => []
    | Comment _ => []
    | LabeledS (_,s) => fields_written s
    
  fun ifc s = 
    case s of 
      Assign (_, Call(f,args)) => [f]
    | Assign (_, _) => []
    | Seq s => List.concat (map ifc s)
    | If (_,a,b) => (ifc a) @ (ifc b)
    | While (gs,g,inv,b) => (ifc gs) @ (ifc b)
    | Break _ => []
    | Block (_,s)=> ifc s
    | Assert _ => []
    | Check _ => []
    | Assume _ => []
    | Comment _ => []
    | LabeledS (_,s) => ifc s
  val impure_functions_called = ifc
  
  local 
    fun inlist eq x [] = false
      | inlist eq x (y::r) = (eq x y) orelse (inlist eq x r)
    fun dedup eq [] = []
      | dedup eq (x::r) = if inlist eq x r then dedup eq r else x::(dedup eq r)
  in
    fun mod_join (a, b) = ModUnion [a, b]
  end
  
  fun alloc t =
    case t of
      StructName st =>
        (case Structtab.lookup st of 
                      SOME (Ast.Struct (n, SOME fields, _, _)) =>
                        ModUnion (map (fn Ast.Field(f,tp, _) => ModField(st,[f])) fields)
                    | _ => ModUnion[])
    | _ => ModUnion []
  fun allocArray t = ModUnion []
  
  
  fun calc_stmt_modifies label c s =
    let val csm = calc_stmt_modifies label c
    in 
      case s of 
        Assign _ => ()
      | Seq ss => List.app csm ss
      | If (e,a,b) => (csm a; csm b)
      | While (gs,g,inv,b) =>
            let val _ = csm b
            val cfuncs = (ifc b) @ (ifc gs)
            val direct = mod_join(ModUnion(map ModField (fields_written b)),
                                  ModUnion(map ModVar (vars_written b)))
            val called = List.foldr mod_join (ModUnion []) (map lookup_modifies cfuncs)
            val _ = bind_while(c, label, mod_join(direct, called))
        in () end
      | Break _ => ()
      | Block (i,s)=> csm s
      | Assert _ => ()
      | Check _ => ()
      | Assume _ => ()
      | Comment _ => ()
      | LabeledS(l,s') => calc_stmt_modifies l c s'
    end
  end
  
  open Syntax
  val rules = 
      [(P("Reach", [VAR "x", VAR "z"]),
             [P("Reach", [VAR"x", VAR"y"]),
              P("FieldReach", [VAR "y", VAR"z"])]),
       (P("Reach", [VAR "x", VAR "x"]),
             [P("ReachSelf", [VAR"x"])]),
       (P("ModReaches", [VAR "f", VAR "t"]),
             [P("ArgReaches",[VAR"f",VAR"s"]),
              P("Reach", [VAR"s", VAR"t"])]),
       (P("Modifies", [VAR "f", VAR "sf"]),
             [P("IsField",[VAR"s",VAR"sf"]),
              P("ModReaches", [VAR"f", VAR"s"]),
              P("ModifiesInt", [VAR"f", VAR"sf"])]),
       (P("ModifiesInt", [VAR "f", VAR "sf"]),
             [P("ModifiesSource",[VAR"f",VAR"sf"])]),
       (P("ModifiesInt", [VAR "f", VAR "sf"]),
             [P("Calls",[VAR"f",VAR"g"]),
              P("Modifies", [VAR"g", VAR"sf"])])
      ]
  fun analyze afuncs =
    let val db = (valOf o Db.new') rules
    fun func_lookup name = 
       List.find (fn x => Symbol.compare(#1 x, name) = EQUAL) afuncs
    val all_structnames = Structtab.list()
    val all_fields = 
      List.concat (map (fn s => case Structtab.lookup s of 
                                   SOME (Ast.Struct (n, SOME fields, _, _)) =>
                                     map (fn Ast.Field(f,tp, _) => (s,[f])) fields (*TODO: add sub-fields*)
                                 | _ => []) all_structnames)
                                 
    fun facts_about_func f 
      (Ast.Function (name, rtp, formals, body, specs, extern, ext)) =
        let val argfacts = 
          List.mapPartial (fn Ast.VarDecl(a,tp,_,_) => 
                                       (case struct_reach_from_tp tp of
                                          SOME s => SOME(Pred.ArgReaches(f,s))
                                        | NONE => NONE)) formals
        val analyzedBody = 
          case (body, extern) of
             (SOME _, false) =>
              (case func_lookup name of 
                    SOME(_,Gcl.Function(_,_,_,_,b,_)) => SOME b
                  | NONE => NONE)
           | _ => NONE
        val fieldfacts =
          map (fn sf => Pred.ModifiesSource (f,sf))
                  (case analyzedBody of
                      SOME b => fields_written b
                    | NONE => all_fields)
        val callfacts = 
          map (fn g => Pred.Calls(f,g)) 
            (case analyzedBody of SOME b => impure_functions_called b
                                | NONE => [])
        in argfacts @ fieldfacts @ callfacts end
    
    val all_funcs = 
     (List.concat (List.map (fn fname =>
        case Symtab.lookup fname of
            SOME (fdesc as Ast.Function _) => [fname]
         | _ => []) (Symtab.list())))
    val _ = Db.add db  
     (List.concat (List.map (fn fname =>
        case Symtab.lookup fname of
            SOME (fdesc as Ast.Function _) => facts_about_func fname fdesc
         | _ => []) (Symtab.list())))
    
    val _ = Db.add db (map Pred.ReachSelf all_structnames)
    val _ = Db.add db (map (fn (s,f) => Pred.IsField(s, (s,f))) all_fields)
    val _ = Db.add db 
      (List.concat (map (fn s => case Structtab.lookup s of 
                                   SOME (Ast.Struct (n, SOME fields, _, _)) =>
                                     List.mapPartial (fn Ast.Field(f,tp, _) => 
                                       (case struct_reach_from_tp tp of
                                          SOME s => SOME(Pred.FieldReach(n,s))
                                        | NONE => NONE)) fields
                                  | _ => []) all_structnames))
    val _ = Db.saturate db
    
     (*For debugging:*)
    fun print_fun_summary f = 
     (AUtil.say ("Summary for " ^ Symbol.name f);
      List.app (AUtil.say o Syntax.print_pred o Pred.inj) (Db.query' db (P("Modifies", [Pred.inj_fun f, VAR"sf"])));
      List.app (AUtil.say o Syntax.print_pred o Pred.inj) (Db.query' db (P("ModifiesSource", [Pred.inj_fun f, VAR"sf"])));
      List.app (AUtil.say o Syntax.print_pred o Pred.inj) (Db.query' db (P("ArgReaches", [Pred.inj_fun f, VAR"sf"])));
      List.app (AUtil.say o Syntax.print_pred o Pred.inj) (Db.query' db (P("Calls", [Pred.inj_fun f, VAR"sf"]))))
    (*
    val _ = List.app print_fun_summary all_funcs*)
      
    fun fun_summary f = 
      let val preds = Db.query' db (P("Modifies", [Pred.inj_fun f, VAR"sf"]))
      val fields = map (fn Pred.Modifies(_,(s,field)) => (s,field)) preds
      in (f, ModUnion(map ModField fields)) end
    val _ = List.app bind_func (map fun_summary all_funcs)
    
    fun calc_modifies (n, Gcl.Function (tp, locs, formals, pre, body, post)) = calc_stmt_modifies ~1 n body
    val _ = List.app calc_modifies afuncs
  in () end
  
end
