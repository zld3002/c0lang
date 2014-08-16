
signature PURITY = 
sig
  (* Note this is not a set because we map each function to the reason it
     needs to be pure*)
  type pureset = VError.error SymMap.map
  
  (* Check the purity of a function, assuming the given set contains the pure
     functions. Returns a list of purity errors, as well as a map of further
     functions that must be considered pure. *)  
  val purity: pureset -> AAst.afunc -> VError.error list * pureset
  
  (* Gives a map from symbols of functions that need purity, to reasons (given
     as Verification Notes) as to why they need purity (this lets us give better
     error messages). *)
  val needspurity: AAst.afunc -> pureset
  
  val bind: pureset -> unit
  val is_pure: Symbol.symbol -> bool
end

structure Purity :> PURITY =
struct
  type pureset = VError.error SymMap.map
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
    structure PairMap = RedBlackMapFn(PairOrd(structure A = SymOrd structure B = SymOrd))
    
    type ctx = {types: Ast.tp SymMap.map,
                locals: etype LocalMap.map,
                fields: etype PairMap.map,
                imms: SymSet.set,
                pures: SymSet.set}
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
     | SOME (Ast.Struct(_, NONE, _,_)) => []
     | _ => []
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
      | FunTypeName(i) => Atom (* ??? Aug 15, 2014 -fp *)
      | FunType _ => Atom (* ??? Aug 15, 2014 -fp *)
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
      | FunTypeName(i) => (ctx, Atom) (* ??? Aug 15, 2014 -fp *)
      | FunType _ => (ctx, Atom)      (* ??? Aug 15, 2014 -fp *)
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
     | Error (e) => ctx 
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
     | While (phi, g, loopinv, modes, b, phi') =>
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

     | AddrOf(f) => Atom
     | Invoke (e, args) => Atom (* do not track *)
      
     | IntConst _ => Atom
     | BoolConst _ => Atom
     | StringConst _ => Atom
     | CharConst _ => Atom
     | Alloc t => tp_extend_mutable(Pointer t)
     | Null => Pt(Mut, Atom)
     | AllocArray (t, e) => tp_extend_mutable(Array t)
     | Cast(t, e) => tp_extend_immutable(t)
     | Select (e, s, f) => C.lookup_field ctx (structofE ctx e) f
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
     | Error e => imms 
     | Annotation (e) => imms
     | Def(l, e) => conassign imms (C.lookup ctx l, syn_extended ctx e)
     | Assign (lv, oper, e) => conassign imms (syn_extended ctx lv, syn_extended ctx e)
     | Expr e => imms
     | Break => imms
     | Continue => imms
     | Return e => imms
     | If (e, a, b, phi) => 
          constraintsP ctx (constraints ctx (constraints ctx imms a) b) phi
     | While (phi, g, loopinv, mods, b, phi') =>
          constraintsP ctx (constraints ctx (constraintsP ctx imms phi) b) phi'
     | MarkedS m => constraints ctx imms (Mark.data m)
     
  fun getlvtag ctx lv =
    case lv of
       Op(DEREF, [a]) =>(case syn_extended ctx a of
                            Pt(tag, e) => tag
                         )
     | Select(e, s, f) => getlvtag ctx e (*TODO: this looks suspicious... -jrk Oct 13*)
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
    
    
  
  val checkEmpty = ([], SymMap.empty)
  fun mergeCheck [] = checkEmpty
    | mergeCheck [x] = x
    | mergeCheck ((e1, m1)::(e2, m2)::rest) =
       let val e = (e1 @ e2, SymMap.unionWith #1 (m1, m2))
       in mergeCheck (e::rest) end
      
    
  fun checkCall mark ctx imms f args =
    case C.isPure ctx f of
       true => checkEmpty (* no constraints in this case *)
     | false => 
         case List.exists (fn a => checkMutability ctx imms 
                                            (syn_extended ctx a))
                            args of
            true => ([], SymMap.insert(SymMap.empty, f, VError.VerificationNote(mark, 
                        "function '" ^ Symbol.name f ^ "' must be pure because it is called on previously allocated state from here")))
          | false => checkEmpty
    
  fun checkE mark ctx imms e =
    case e of
       Local l => checkEmpty
     | Op (oper, args) =>
         mergeCheck (map (fn e =>checkE mark ctx imms e) args)
     | Call (f, args) => 
         let val errs = mergeCheck (map (fn e =>checkE mark ctx imms e) args)
         in mergeCheck[errs, checkCall mark ctx imms f args] end
     | AddrOf _ => checkEmpty
     | Invoke (e, args) =>
         mergeCheck (map (fn e => checkE mark ctx imms e) (e::args))
     | IntConst _ => checkEmpty
     | BoolConst _ => checkEmpty
     | StringConst _ => checkEmpty
     | CharConst _ => checkEmpty
     | Alloc _ => checkEmpty
     | Null => checkEmpty
     | Result => checkEmpty
     | Length e' => checkE mark ctx imms e'
     | Hastag(tp, e') => checkE mark ctx imms e'
     | AllocArray (tp, e') => checkE mark ctx imms e'
     | Cast(tp, e') => checkE mark ctx imms e'
     | Select (e', s, field) => checkE mark ctx imms e'
     | MarkedE (m) => checkE (Mark.ext m) ctx imms (Mark.data m)
     
  fun check mark ctx imms s = 
    case s of     
       Nop => checkEmpty
     | Seq (a,b) => mergeCheck [check mark ctx imms a, check mark ctx imms b]
     | Assert (e) => checkE mark ctx imms e
     | Annotation (e) => checkEmpty
     | Error (e) => checkE mark ctx imms e 
     | Def(l, e) => checkE mark ctx imms e
     | Assign (lv, oper, e) =>
         mergeCheck
         [if isImm (imms, getlvtag ctx lv)
          then ([VError.VerificationError(mark, 
                 "function may assign to previously allocated memory")], SymMap.empty)
          else checkEmpty, checkE mark ctx imms e, checkE mark ctx imms lv]
                    
     | Expr e => (checkE mark ctx imms e)
     | Break => checkEmpty
     | Continue => checkEmpty
     | Return (SOME e) => (checkE mark ctx imms e)
     | Return (NONE) => checkEmpty
     | If (e, a, b, phi) => 
         mergeCheck [checkE mark ctx imms e,
                     check mark ctx imms a,
                     check mark ctx imms b]
     | While (phi, g, loopinv, mods, b, phi') =>
         mergeCheck[checkE mark ctx imms g, check mark ctx imms b]
     | MarkedS m => check (Mark.ext m) ctx imms (Mark.data m)
     
  
  fun purity puremap (Function(rtp, name, tps, formals, reqs, body, ens)) =
    let fun markAndBindArg ((_, t, loc), c) =
          let val (c', et) = tp_extend_imm_rec c t
          in C.bind c' loc et end
        val purefuncs = SymSet.addList(SymSet.empty, map (#1) (SymMap.listItemsi puremap))
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
        val (errors, newset) = check NONE ctx imms body
        val reason = valOf(SymMap.find(puremap, name))
    in (case errors of
           [] => []
         | a => a @ [reason], newset) end
  
  fun needspurityE e = 
    case e of
       Local l => []
     | Op (oper, args) => (List.concat (map needspurityE args))
     | Call (f, args) =>
         [SymMap.insert(SymMap.empty, f,
                    VError.VerificationNote (NONE, "function '" ^ Symbol.name f ^ "' must be pure because it is called in an annotation from here"))]
          @ (List.concat (map needspurityE args))
     | AddrOf (f) => [] (* do not track *)
     | Invoke (e, args) =>
         (* warning: e computes to a function which may not be pure; do not track *)
         List.concat (map needspurityE (e::args))
     | IntConst _ => []
     | BoolConst _ => []
     | StringConst _ => []
     | CharConst _ => []
     | Alloc _ => []
     | Null => []
     | Result => []
     | Length e' => needspurityE e'
     | Hastag(tp, e') => needspurityE e'
     | AllocArray (tp, e') => needspurityE e'
     | Cast(tp, e') => needspurityE e'
     | Select (e', s, field) => needspurityE e'
     | MarkedE (m) =>
        let val np = needspurityE (Mark.data m)
        in map (SymMap.map (fn e => VError.enclose e (Mark.ext m))) np end
       
  fun needspurityS s = 
    case s of 
       Nop => []
     | Seq (a, b) => (needspurityS a) @ (needspurityS b)
     | Assert e => [] (* assert(e) is not an "annotation" *)
     | Error e => [] 
     | Annotation e => needspurityE e
     | Def _ => []
     | Assign _ => []
     | Expr _ => []
     | Break => []
     | Continue => []
     | Return _ => []
     | If (e, a, b, p) => (needspurityS a) @ (needspurityS b)
     | While (p, a, invs, mods, b, p') =>
         (List.concat (map needspurityE invs)) @ (needspurityS b)
     | MarkedS m => needspurityS (Mark.data m)
     
  fun needspurity (Function(rtp, name, tps, formals, reqs, body, ens)) =
    foldr (SymMap.unionWith #1) SymMap.empty
       (
         (List.concat (map needspurityE reqs)) @
         (needspurityS body) @
         (List.concat (map needspurityE ens))
       )
  val pures = ref (SymMap.empty: pureset)
  fun bind ps = (pures := ps)
  fun is_pure f = 
    case SymMap.find(!pures,f) of
       SOME _ => true
     | NONE => false
end
