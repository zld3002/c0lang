
signature PURITY = 
sig
  val purity: SymSet.set -> AAst.afunc -> VError.error list
  val needspurity: AAst.afunc -> SymSet.set
end

structure Purity =
struct
  type sym = Symbol.symbol
  type ident = string
  
  open Ast
  open AAst
  
  datatype tag = Imm | Mut | Inferred of int | Join of tag list
  datatype etype = Atom | Pt of tag * etype | Arr of tag * etype | St of sym
  
  fun pp_tag t = 
    case t of
       Imm => "i"
     | Mut => "m"
     | Inferred i => "?" ^ Int.toString i
     | Join l => "(" ^ AAst.Print.commas "/\\" (map pp_tag l) ^ ")"
  fun pp_etype e = 
    case e of 
       Atom => "$"
     | Pt(t, tp) => pp_etype tp ^ " ("^pp_tag t^")*"
     | Arr(t, tp) => pp_etype tp ^ " ("^pp_tag t^")[]"
     | St s => "struct "^Symbol.name s
  structure C = 
  struct
    structure PairMap = RedBlackMapFn(struct type ord_key = sym*sym
                                      fun compare ((ast,af),(bs,bf)) =
                                        case Symbol.compare(ast,bs) of
                                           EQUAL => Symbol.compare(af,bf)
                                         | r => r
                                      end
                                     )
    type ctx = {types: Ast.tp SymMap.map, locals: etype LocalMap.map, fields: etype PairMap.map, imms: SymSet.set, pures: SymSet.set}
    fun empty (tps,pures) = {types = tps, locals = LocalMap.empty, fields=PairMap.empty, imms = SymSet.empty, pures = pures}
    fun is_struct_imm (ctx:ctx) s = SymSet.member(#imms ctx, s)
    fun mark_struct_imm (ctx:ctx) s = {imms = SymSet.add(#imms ctx, s),
                                       locals = #locals ctx,
                                       types = #types ctx,
                                       fields = #fields ctx,
                                       pures = #pures ctx}
    fun typeof (ctx:ctx) s = valOf(SymMap.find(#types ctx, s))
    fun bind (ctx:ctx) l et =
      {locals = LocalMap.insert(#locals ctx, l, et),
       types = #types ctx,
       fields= #fields ctx,
       imms = #imms ctx,
       pures = #pures ctx}
    fun lookup (ctx:ctx) l = 
      case LocalMap.find(#locals ctx, l) of
         SOME etp => etp
       | NONE => raise Fail ("unknown local " ^ AAst.Print.pp_loc l)
    fun bind_field (ctx:ctx) s f et =
      {fields = PairMap.insert(#fields ctx, (s,f), et),
       types = #types ctx,
       locals= #locals ctx,
       imms = #imms ctx,
       pures = #pures ctx}
    fun lookup_field (ctx:ctx) s f = valOf(PairMap.find(#fields ctx, (s,f)))
    fun toString (ctx:ctx) =
      let val s = map (fn (l, etype) => AAst.Print.pp_loc l ^": "^ pp_etype etype) (LocalMap.listItemsi (#locals ctx))
          val s' = map (fn ((s,f), etype) => Symbol.name s ^"."^Symbol.name f ^": "^ pp_etype etype) (PairMap.listItemsi (#fields ctx))
      in AAst.Print.commas "\n" s ^"\n"^ AAst.Print.commas "\n" s' end
    fun isPure (ctx:ctx) s = SymSet.member(#pures ctx, s)
  end
  
  
  local 
    val r = ref 0
  in
    fun freshtag () = Inferred(!r) before r := !r+1
  end
  
  fun struct_fields s =
    case Structtab.lookup s of
       SOME (Ast.Struct(_, SOME fields,_,_)) =>
          map (fn (Field (i, t, _)) => (i,t)) fields
  
  fun tp_extend f tp =
     case tp of
        Int	=> Atom
      | Bool => Atom
      | String => Atom
      | Char => Atom
      | Pointer(t) => Pt(f(), tp_extend f t)
      | Array(t) => Arr(f(), tp_extend f t)
      | StructName(i) => St(i)
      | TypeName(i) => tp_extend f (Syn.expand_all tp)
      | Void => Atom
      | Any => Atom
      
  fun tp_extend_fresh tp = tp_extend freshtag tp
  fun tp_extend_mutable tp = tp_extend (fn _ => Mut) tp
  fun tp_extend_immutable tp = tp_extend (fn _ => Imm) tp
      
  fun tp_extend_imm_rec ctx tp =
     case tp of
        Int	=> (ctx, Atom)
      | Bool => (ctx, Atom)
      | String => (ctx, Atom)
      | Char => (ctx, Atom)
      | Pointer(t) => let val (c', et) =  tp_extend_imm_rec ctx t
                      in (c', Pt(Imm, et)) end
      | Array(t) => let val (c', et) =  tp_extend_imm_rec ctx t
                    in (c', Arr(Imm, et)) end
      | StructName(i) => (mark_struct_imm ctx i, St(i))
      | TypeName(i) => tp_extend_imm_rec ctx (Syn.expand_all tp)
      | Void => (ctx, Atom)
      | Any => (ctx, Atom)
  and mark_struct_imm ctx s =
     case C.is_struct_imm ctx s of
        true => ctx
      | false => 
         let val ctx' = C.mark_struct_imm ctx s
             val ctx'' = foldl (fn ((i,t),c) => 
                                  let val (ctx, et) = tp_extend_imm_rec c t
                                  in C.bind_field ctx s i et end)
                         ctx' (struct_fields s)
         in ctx'' end
         
  and mark_struct_fresh ctx s =
     case C.is_struct_imm ctx s of
        true => ctx
      | false =>
         let val ctx' = foldl (fn ((i,t),c) => 
                                  let val et = tp_extend_fresh t
                                  in C.bind_field c s i et end)
                         ctx (struct_fields s)
         in ctx' end
         
  fun buildContextPhis ctx [] = ctx
    | buildContextPhis ctx (p::ps) = 
         let val PhiDef(sym, i, _) = p
             val tp = C.typeof ctx sym
             val ctx' = C.bind ctx (sym,i) (tp_extend_fresh tp)
         in buildContextPhis ctx' ps end
    
  fun buildContext ctx s =
    case s of     
       Nop => ctx
     | Seq (a,b) => 
         buildContext (buildContext ctx a) b
     | Assert (e) => ctx
     | Annotation (e) => ctx
     | Def((sym,i),e) => 
         let val tp = C.typeof ctx sym
             val ctx' = C.bind ctx (sym,i) (tp_extend_fresh tp)
         in ctx' end
     | Assign (lv, oper, e) => ctx
     | Expr e => ctx
     | Break => ctx
     | Continue => ctx
     | Return e => ctx
     | If (e, a, b, phi) => 
         buildContextPhis (buildContext (buildContext ctx a) b) phi
     | While (phi, g, loopinv, b, phi') =>
         buildContextPhis (buildContext ctx b) (phi@phi')
     | MarkedS m => buildContext ctx (Mark.data m)
   
          
	fun syn_join(a,b) =
	  case (a,b) of 
	     (Pt (t,e), Pt(t',e')) => Pt(Join[t,t'], syn_join(e,e'))
	   | (Arr (t,e), Arr(t',e')) => Arr(Join[t,t'], syn_join(e,e'))
	   | (Atom, b) => b
	   | (a, Atom) => a
	   | (St a, St _) => St a
	   
	fun rtpofF f = 
	  (case Symtab.lookup f of
         SOME(Ast.Function(g', rtp, params, _, _, _, _)) => rtp)
  fun structofE ctx e =
      (case (syn_extended ctx e) of 
         St(s) => s)
  and syn_extended ctx e =
    case e of 
       Local (l) => C.lookup ctx l
     | Op(Ast.SUB, [e1,e2]) =>
         (case (syn_extended ctx e1) of Arr(tag, tp) => tp)
     | Op(Ast.DEREF, [e1]) =>
         (case (syn_extended ctx e1) of Pt(tag, tp) => tp)
     | Op(Ast.COND, [e1, e2, e3]) =>
         syn_join (syn_extended ctx e2, syn_extended ctx e3)
     | Op(oper,es) => Atom (* all remaining operators give atoms *)
                     
     | Call (f, args) => 
        (case C.isPure ctx f of
            true => tp_extend_immutable (rtpofF f)
          | false => tp_extend_mutable (rtpofF f))
      
     | IntConst _ => Atom
     | BoolConst _ => Atom
     | StringConst _ => Atom
     | CharConst _ => Atom
     | Alloc t => tp_extend_mutable(Pointer t)
     | Null => Pt(Mut, Atom)
     | AllocArray (t, e) => tp_extend_mutable(Array t)
     | Select (e, f) => C.lookup_field ctx (structofE ctx e) f
     | MarkedE m => syn_extended ctx (Mark.data m)
  
  
  structure IntSet = IntBinarySet
  val immempty = IntSet.empty
  fun isImm(imms, tag) = 
    case tag of
       Imm => true
     | Mut => false
     | Inferred(i) => IntSet.member(imms, i)
     | Join(tags) => List.exists (fn i => isImm(imms, i)) tags
  
  fun immAdd(imms, tag) = 
    case tag of 
       Inferred(i) => IntSet.add(imms, i)
     | _ => imms
  
  fun conassign imms (a,b) =
    case (a,b) of
       (Pt(t1, et1), Pt(t2, et2)) =>
         let val imms' = if isImm(imms,t1) orelse 
                            isImm(imms,t2)
                         then immAdd(immAdd(imms,t1), t2)
                         else imms
         in conassign imms' (et1, et2) end
     | (Arr(t1, et1), Arr(t2, et2)) => 
         let val imms' = if isImm (imms,t1) orelse 
                            isImm(imms,t2)
                         then immAdd(immAdd(imms,t1), t2)
                         else imms
         in conassign imms' (et1, et2) end
     | _ => imms
     
  fun constraintsP ctx imms [] = imms
    | constraintsP ctx imms (PhiDef(sym, i, []) :: ps) =
         constraintsP ctx imms ps
    | constraintsP ctx imms (PhiDef(sym, i, i'::l) :: ps) =
         let val imms' = conassign imms (C.lookup ctx (sym,i), C.lookup ctx (sym,i')) 
         in constraintsP ctx imms' (PhiDef(sym, i, l) :: ps) end
         
  fun constraints ctx imms s = 
    case s of     
       Nop => imms
     | Seq (a,b) => constraints ctx (constraints ctx imms a) b
     | Assert (e) => imms
     | Annotation (e) => imms
     | Def(l, e) => conassign imms (C.lookup ctx l, syn_extended ctx e)
     | Assign (lv, oper, e) => conassign imms (syn_extended ctx lv, syn_extended ctx e)
     | Expr e => imms
     | Break => imms
     | Continue => imms
     | Return e => imms
     | If (e, a, b, phi) => 
          constraintsP ctx (constraints ctx (constraints ctx imms a) b) phi
     | While (phi, g, loopinv, b, phi') =>
          constraintsP ctx (constraints ctx (constraintsP ctx imms phi) b) phi'
     | MarkedS m => constraints ctx imms (Mark.data m)
     
  fun getlvtag ctx lv =
    case lv of
       Op(DEREF, [a]) =>(case syn_extended ctx a of
                            Pt(tag, e) => tag
                         )
     | Select(e, f) => getlvtag ctx e
     | Local(l) => Mut
     | Op(SUB, [a, i]) => (case syn_extended ctx a of
                            Arr(tag, e) => tag
                           )
     | MarkedE(m) => getlvtag ctx (Mark.data m)
  
     
  fun checkMut ctx imms v tp =
     case tp of
        Atom => (v, false)
      | Pt(t, tp) => if isImm (imms, t)
                     then (v, true)
                     else checkMut ctx imms v tp
      | Arr(t, tp) =>if isImm (imms, t)
                     then (v, true)
                     else checkMut ctx imms v tp
      | St s => checkMutStruct ctx imms v s
  and checkMutStruct ctx imms v s =
     case SymSet.member(v,s) of
        true => (v, false)
      | false => 
         let val v' = SymSet.add(v, s)
             fun checkfield ((field, _), (v, isimm)) = 
                   if isimm then (v, true)
                            else checkMut ctx imms v (C.lookup_field ctx s field)
             val res = foldl checkfield
                         (v', false) (struct_fields s)
         in res end
         
  fun checkMutability ctx imms tp = #2(checkMut ctx imms SymSet.empty tp)
    
  fun checkCall mark ctx imms f args =
    case C.isPure ctx f of
       true => [] (* no constraints in this case *)
     | false => 
         let val immutables = (map (fn a => checkMutability ctx imms (syn_extended ctx a)) args)
         in
           case List.foldl (fn (a,b) => a orelse b) false immutables of
              true => [VError.VerificationError(mark, "cannot call impure function which may modify previously visible memory.")]
            | false => []
         end  
    
  fun checkE mark ctx imms e =
    case e of
       Local l => []
     | Op (oper, args) =>
         List.concat (map (fn e =>checkE mark ctx imms e) args)
     | Call (f, args) => 
         let val errs = List.concat (map (fn e =>checkE mark ctx imms e) args)
         in errs @ (checkCall mark ctx imms f args) end
     | IntConst _ => []
     | BoolConst _ => []
     | StringConst _ => []
     | CharConst _ => []
     | Alloc _ => []
     | Null => []
     | Result => []
     | Length e' => checkE mark ctx imms e'
     | Old e' => checkE mark ctx imms e'
     | AllocArray (tp, e') => checkE mark ctx imms e'
     | Select (e', field) => checkE mark ctx imms e'
     | MarkedE (m) => checkE (Mark.ext m)  ctx imms (Mark.data m)
     
  fun check mark ctx imms s = 
    case s of     
       Nop => []
     | Seq (a,b) => (check mark ctx imms a) @ (check mark ctx imms b)
     | Assert (e) => checkE mark ctx imms e
     | Annotation (e) => []
     | Def(l, e) => checkE mark ctx imms e
     | Assign (lv, oper, e) =>
                   (if isImm (imms, getlvtag ctx lv)
                    then [VError.VerificationError(mark, 
                           "assignment may modify previously visible memory.")]
                    else []) @ (checkE mark ctx imms e) @ (checkE mark ctx imms lv)
                    
     | Expr e => (checkE mark ctx imms e)
     | Break => []
     | Continue => []
     | Return (SOME e) => (checkE mark ctx imms e)
     | Return (NONE) => []
     | If (e, a, b, phi) => 
          (checkE mark ctx imms e) @ 
          (check mark ctx imms a) @
          (check mark ctx imms b)
     | While (phi, g, loopinv, b, phi') =>
          (checkE mark ctx imms g) @
          (check mark ctx imms b)
     | MarkedS m => check (Mark.ext m) ctx imms (Mark.data m)
     
  
  fun purity purefuncs (Function(rtp, name, tps, formals, reqs, body, ens)) =
    let fun markAndBindArg ((_, t, loc), c) =
          let val (c', et) = tp_extend_imm_rec c t
          in C.bind c' loc et end
        val ctxArgs = foldl markAndBindArg (C.empty (tps, purefuncs)) formals
        (* HACKITY HACK: add all structs to the context, so that we never ask
           the context about something it hasn't seen before. *)
        val ctxAll = foldl (fn (name, c) => mark_struct_fresh c name)
                     ctxArgs (Structtab.list())
        val ctx = buildContext ctxAll body
        fun iter imms =
           let  val imms' = constraints ctx imms body
           in if IntSet.equal(imms, imms')
              then imms
              else iter imms'
           end
        val imms = iter immempty
        val errors = check NONE ctx imms body
    in errors end
  
  fun needspurityE e = 
    case e of
       Local l => []
     | Op (oper, args) => (List.concat (map needspurityE args))
     | Call (f, args) => [f] @ (List.concat (map needspurityE args))
     | IntConst _ => []
     | BoolConst _ => []
     | StringConst _ => []
     | CharConst _ => []
     | Alloc _ => []
     | Null => []
     | Result => []
     | Length e' => needspurityE e'
     | Old e' => needspurityE e'
     | AllocArray (tp, e') => needspurityE e'
     | Select (e', field) => needspurityE e'
     | MarkedE (m) => needspurityE (Mark.data m)
       
  fun needspurityS s = 
    case s of 
       Nop => []
     | Seq (a, b) => (needspurityS a) @ (needspurityS b)
     | Assert e => [] (* assert(e) is not an "annotation" *)
     | Annotation e => needspurityE e
     | Def _ => []
     | Assign _ => []
     | Expr _ => []
     | Break => []
     | Continue => []
     | Return _ => []
     | If (e, a, b, p) => (needspurityS a) @ (needspurityS b)
     | While (p, a, invs, b, p') =>
         (List.concat (map needspurityE invs)) @ (needspurityS b)
     | MarkedS m => needspurityS (Mark.data m)
     
  fun needspurity (Function(rtp, name, tps, formals, reqs, body, ens)) =
    foldr SymSet.add' SymSet.empty
       (
         (List.concat (map needspurityE reqs)) @
         (needspurityS body) @
         (List.concat (map needspurityE ens))
       )
end
