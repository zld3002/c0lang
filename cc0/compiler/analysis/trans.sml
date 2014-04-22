
structure Trans = struct

open Gcl
structure A = Ast


val resultVar = Symbol.symbol "\\result"

type context = Mark.ext option * A.tp Symbol.table * tp SymMap.map ref * Ast.tp
fun declareVar ((_,_,vars, _):context) (v,t) = (vars := SymMap.insert(!vars, v,t))
fun varType ((_,_,vars, _):context) (v) = 
   case SymMap.find(!vars, v) of 
     SOME tp => tp
   | NONE => raise Fail ("could not find " ^ Symbol.name v)
fun inRegion ((_,x,y,z):context) (SOME m) = (SOME m,x,y,z)
  | inRegion c NONE = c
fun returnType (_,tc,_,rtp) = rtp
fun typeContext (_,tc,_,rtp) = tc
fun currentRegion (SOME m,_,_,_) = m
  | currentRegion (NONE,_,_,_) = ((0,0),(0,0),"")

local val temp = ref 0 in
    fun freshVar ctx tp =
      let val newsym = (Symbol.new ("t"^ (Int.toString (!temp)))) before (temp := !temp + 1)
      in (declareVar ctx (newsym, tp); newsym) end
end


local val temp = ref 0 in
    fun newLabel() = !temp before temp := !temp + 1
end

local
    structure IM = IntRedBlackMap 
    val map = ref (IM.empty : Mark.ext IM.map)
    val assertmsgmap = ref (IM.empty : string IM.map)
in
    fun labelExt l (SOME m) = map := (IM.insert(!map, l, m))
      | labelExt l (NONE) = ()
    fun labelAssertMsg l msg = assertmsgmap := (IM.insert(!assertmsgmap, l, msg))
    fun lookupExt l = IM.find(!map, l)
    fun lookupMsg l = IM.find(!assertmsgmap, l)
end

fun regionOfExpr e = 
  case e of 
     A.Marked e => Mark.ext e
   | _ => NONE

fun binop_assert' LShift (x,y) = Assert(ValOp(And,[Rel(Geq, Int, Make.I 0, y),
                                                   Rel(Less, Int, y, Make.I 32)]))
  | binop_assert' RShift (x,y) = binop_assert' LShift (x,y)
  | binop_assert' Div (x,y) = Assert(ValOp(And,[Rel(Neq, Int, Make.I 0, y),
                                        ValOp(Or,[Rel(Neq, Int, Make.I ~1, y),
                                          Rel(Neq, Int, x, ValOp(IntConst Word32Signed.TMIN,[]))])]))
  | binop_assert' Mod (x,y) = binop_assert' Div (x,y)
  | binop_assert' _ (x,y) = Seq[]
fun binop_assert a b = 
    case binop_assert' a b of
       Assert(x) => Seq[Assert(x), Assume (x)]
     | Seq[] => Seq[]
  
fun deref_assert (p, region) =
   let val label = newLabel()
       val _ = labelExt label region
       val _ = labelAssertMsg label "unprotected pointer dereference"
       val tp = case tp_of p of Pointer t => t
   in Seq[LabeledS(label, Assert(Rel(Neq, Pointer tp, p, Null (tp)))), Assume(Rel(Neq, Pointer tp, p, Null (tp)))] end

fun var ctx v = Var(v, varType ctx v)

fun infered_type ctx e = (Syn.syn_exp (typeContext ctx) e)

(* Only defined for operations which can be in an assignment, like +=, *=, etc. *)
fun trans_oper A.PLUS = Addition
  | trans_oper A.MINUS = Subtract
  | trans_oper A.TIMES = Mult
  | trans_oper A.DIVIDEDBY = Div
  | trans_oper A.MODULO = Mod
  | trans_oper A.AND = Bitand
  | trans_oper A.XOR = Bitxor
  | trans_oper A.OR = Bitor
  | trans_oper A.SHIFTLEFT = LShift
  | trans_oper A.SHIFTRIGHT = RShift

fun trans_expr ctx e tp = 
  let val trPure = trans_expr_pure ctx 
      fun trInt e = trPure e A.Int
      fun trBool e = trPure e A.Bool
      fun pureop (oper, args) = 
            let val (effects, exprs) = ListPair.unzip args in
            (Seq effects, ValOp(oper, exprs)) end
      fun rel (oper, tp, args) = 
            let val (effects, [e1,e2]) = ListPair.unzip args in
            (Seq effects, Rel(oper, tp, e1, e2)) end
  in
  case e of
     A.Var v => (Seq[],var ctx v)
   | A.IntConst i => (Seq[],ValOp(IntConst i,[]))
   | A.StringConst s => (Seq[],ValOp(StringConst s,[]))
   | A.CharConst c => (Seq[],ValOp(CharConst c,[]))
   | A.True => (Seq[],ValOp(BoolConst true,[]))
   | A.False => (Seq[], ValOp(BoolConst false,[]))
   | A.Null => (Seq[], Null (case (Make.make_tp tp) of Pointer t => t))
   | A.OpExp _ =>
      (case e of 
          A.OpExp(A.SUB, [a,i]) => 
               let val (adn,aup) = trPure a (A.Array tp)
                   val (idn,iup) = trInt i
               in (Seq[adn, idn], Make.sub (aup, iup)) end
        | A.OpExp(A.DEREF, [p]) => 
               let val (pdn, pup) = trPure p (A.Pointer tp)
               in (Seq[pdn, deref_assert(pup, SOME(currentRegion ctx))], Make.deref(pup)) end
       
        | A.OpExp(A.LOGAND, [a,b]) => 
               let val ((adn, aup), (bdn,bup)) = (trBool a, trBool b)
               in (Seq[adn, If(aup,bdn,Seq[])], ValOp(And, [aup, bup])) end
        | A.OpExp(A.LOGOR,  [a,b]) => 
               let val ((adn, aup), (bdn,bup)) = (trBool a, trBool b)
               in (Seq[adn, If(aup,Seq[],bdn)], ValOp(Or, [aup, bup])) end
        
        | A.OpExp(A.COND, [c,a,b]) =>
               let val ((cdn,cup), (adn,aup),   (bdn,bup)  )  =
                       (trBool c,  trPure a tp, trPure b tp)
               in (Seq[cdn, If(cup,adn,bdn)], ValOp(Cond, [cup, aup, bup])) end
        
        | A.OpExp(A.SHIFTLEFT, [e,k]) => 
               let val ((edn, eup), (kdn,kup)) = (trInt e, trInt k)
               in (Seq[edn, kdn, binop_assert LShift (eup,kup)],
                                      ValOp(LShift, [eup, kup])) end
        | A.OpExp(A.SHIFTRIGHT, [e,k]) => 
               let val ((edn, eup), (kdn,kup)) = (trInt e, trInt k)
               in (Seq[edn, kdn, binop_assert RShift (eup,kup)],
                                      ValOp(RShift, [eup, kup])) end
       
        | A.OpExp(A.DIVIDEDBY, [e,k]) => 
               let val ((edn, eup), (kdn,kup)) = (trInt e, trInt k)
               in (Seq[edn, kdn, binop_assert Div (eup, kup)],
                                      ValOp(Div, [eup, kup])) end
        | A.OpExp(A.MODULO, [e,k]) => 
               let val ((edn, eup), (kdn,kup)) = (trInt e, trInt k)
               in (Seq[edn, kdn, binop_assert Mod (eup, kup)],
                                      ValOp(Mod, [eup, kup])) end
       
        | A.OpExp(A.LOGNOT, [a]) => pureop(Not, [trBool a]) 
        | A.OpExp(A.PLUS, [x,y]) => pureop(Addition, [trInt x, trInt y])
        | A.OpExp(A.MINUS, [x,y]) => pureop(Subtract, [trInt x, trInt y])
        | A.OpExp(A.TIMES, [x,y]) => pureop(Mult, [trInt x, trInt y])
        | A.OpExp(A.AND, [x,y]) => pureop(Bitand, [trInt x, trInt y])
        | A.OpExp(A.OR, [x,y]) => pureop(Bitor, [trInt x, trInt y])
        | A.OpExp(A.XOR, [x,y]) => pureop(Bitxor, [trInt x, trInt y])
        | A.OpExp(A.COMPLEMENT, [x,y]) => pureop(Complement, [trInt x, trInt y])
        | A.OpExp(A.NEGATIVE, [x]) => pureop(Negation, [trInt x])
         
        (*TODO: allow char comparisions here as well. *)
        | A.OpExp(A.LESS, [x,y]) => rel(Less, Int, [trInt x, trInt y])
        | A.OpExp(A.GREATER, [x,y]) => rel(Greater, Int, [trInt x, trInt y])
        | A.OpExp(A.GEQ, [x,y]) => rel(Geq, Int, [trInt x, trInt y])
        | A.OpExp(A.LEQ, [x,y]) => rel(Leq, Int, [trInt x, trInt y])
        | A.OpExp(A.EQ, [x,y]) =>
            let val tpx = (Syn.syn_exp (typeContext ctx) x)
                val tpy = (Syn.syn_exp (typeContext ctx) y)
                val join = Syn.lub tpx tpy
                val tp = case join of A.Pointer A.Any => A.Pointer A.Int | _ => join
            in rel(Eq, Make.make_tp tp, [trPure x tp, trPure y tp]) end
        | A.OpExp(A.NOTEQ, [x,y]) =>
            let val tpx = Syn.syn_exp (typeContext ctx) x
                val tpy = Syn.syn_exp (typeContext ctx) y
                val join = Syn.lub tpx tpy
                val tp = case join of A.Pointer A.Any => A.Pointer A.Int | _ => join
            in rel(Neq, Make.make_tp tp, [trPure x tp, trPure y tp]) end
        | _ => raise Fail ("unknown operExpr" ^ Ast.Print.pp_exp e)
      )  
   | A.Select(strct, field) => (* Note that we do not use trans_expr_pure here.
                                  this is because a struct is not a valid expression
                                  in the target language, so we cannot capture it.
                                  instead, we can have a certain number of fields,
                                  up to a dereference or an array access. Currently
                                  structs in arrays is broken.
                                  
                                  TODO: check that this actually works as intended.*)
        let val (sdn, sup) = trans_expr ctx strct (infered_type ctx strct) in
        (sdn, Make.select_single(sup, field)) end
   | A.FunCall(f, args) => 
        let val SOME(A.Function(_, returntype, formals, _, specs, extern, _)) = Symtab.lookup f
            val argtypes = map (fn A.VarDecl(_,t,_,_) => t) formals
            val args = ListPair.map (fn (a,t) => trans_expr_pure ctx a t) (args,argtypes)
            val (argdn,argup) = ListPair.unzip args
            val rtp = Make.make_tp returntype
            val t = freshVar ctx rtp
        in case Purity.is_pure f of
              true => (Seq argdn, ValOp(PureCall (f, rtp), argup))
            | false => (Seq (argdn @ [Assign(Local t, Call (f, argup))]), Var (t, rtp))  end
   | A.Alloc cell_type =>
        let val tp = Make.make_tp cell_type
            val t = freshVar ctx (Pointer tp)
        in (Assign(Local t, Alloc(tp)), Var (t, Pointer tp)) end 
   | A.AllocArray (elem_type, size) =>
        let val tp = Make.make_tp elem_type
            val t = freshVar ctx (Array tp)
            val (sdn, sup) = trInt size
        in (Seq[sdn,Assign(Local t, AllocArray(tp, sup))], Var (t, Array tp)) end
   | A.Result => (Seq[], Var (resultVar, Make.make_tp (returnType ctx)))
   | A.Length e => pureop(Length, [trans_expr ctx e (A.Array A.Any)])
   (*| A.Old of exp          (* \old(e), in @ensures *)*)
   | A.Marked m => 
       let val l = newLabel()
           val _ = labelExt l (Mark.ext m)
           val (dn, up) = trans_expr (inRegion ctx (Mark.ext m)) (Mark.data m) tp
       in (LabeledS(l, dn), up) end
   end


and trans_expr_pure ctx rhs tp = 
  let val (edn, eup) = trans_expr ctx rhs tp
  
      (* Note: here pure means "heap independent", as there are no side effects of
         expressions in the target language. *)
      fun isPure (Var _) = true
        | isPure (Rel(_,_,x,y)) = isPure x andalso isPure y
        | isPure (ValOp(_,args)) = List.all isPure args
        | isPure (Null _) = true
        | isPure _ = false
  in
    case isPure eup of 
       true => (edn, eup)
     | false =>
         let val tp = tp_of eup val t = freshVar ctx tp
         in (Seq[edn,Assign(Local t, Expr eup)], Var (t, tp)) end
  end   

fun trans_expr_bool ctx e = trans_expr ctx e A.Bool

fun trans_expr_var ctx e = 
  let val (edn, eup) = trans_expr ctx e (infered_type ctx e)
  in
    case eup of 
       Var(v, tp) => (edn, v)
     | _ =>
         let val tp = tp_of eup val t = freshVar ctx tp
         in (Seq[edn,Assign(Local t, Expr eup)], t) end
  end   

fun trans_assert ctx e = 
  let fun IfNonDet(a,b) = If(ValOp(Nondet,[]), a, b)
      val False = ValOp(BoolConst false,[])
      fun LogNot x = ValOp(Not,[x])
      fun LabelExtAll ext (a,b,c,d,e) = 
            let val l = newLabel()
                val _ = labelExt l ext
            in (LabeledS (l,a), LabeledS (l,b), LabeledS (l,c),
                LabeledS (l,d), LabeledS (l,e)) end
  in 
  case e of
     A.True => (Seq[], Seq[], Assert(False), Seq[], Assume(False))
   | A.False => (Seq[], Assert(False), Seq[], Assume(False), Seq[])
   | A.OpExp(A.LOGAND, [a,b]) => trans_assert ctx (A.OpExp(A.COND, [a,b, A.False]))
   | A.OpExp(A.LOGOR,  [a,b]) => trans_assert ctx (A.OpExp(A.COND, [a,A.True, b]))
   | A.OpExp(A.COND, [c,a,b]) =>
       let val (awf, atc, afc, atrue, afalse) = trans_assert ctx a
           val (bwf, btc, bfc, btrue, bfalse) = trans_assert ctx b
           val (cwf, ctc, cfc, ctrue, cfalse) = trans_assert ctx c
       in 
           (Seq[cwf,IfNonDet(Seq[ctrue,awf],Seq[cfalse,bwf])],
            IfNonDet(Seq[ctrue, atc], Seq[cfalse, btc]),
            IfNonDet(Seq[ctrue, afc], Seq[cfalse, bfc]),
            IfNonDet(Seq[ctrue, atrue], Seq[cfalse, btrue]),
            IfNonDet(Seq[ctrue, afalse], Seq[cfalse, bfalse])
           )
       end
   | A.OpExp(A.LOGNOT, [a]) => 
       let val (wf, atc, afc, atrue, afalse) = trans_assert ctx a
       in (wf, afc, atc, afalse, atrue) end
   | A.Marked m => 
         LabelExtAll (Mark.ext m) (trans_assert (inRegion ctx (Mark.ext m)) (Mark.data m))
   | _ => 
       let val (edn, eup) = trans_expr_bool ctx e
           fun transform s = case s of 
                                If(e,a,b) => If(e, transform a, transform b)
                              | Assume e => s
                              | Assert e => Assume e
                              | Assign _ => s
                              | Seq ss => Seq(map transform ss)
                              | LabeledS(l, s) => LabeledS(l, transform s)
       in (edn, Seq[transform edn, Assert(eup)], Seq[transform edn, Assert(LogNot eup)],
                Seq[transform edn, Assume(eup)], Seq[transform edn, Assume(LogNot eup)]) 
       end
   end
   
fun trans_annos ctx [] = Anno(Seq[],Seq[],Seq[])
  | trans_annos ctx ((e,ext) :: rest) = 
      let val Anno (rwf, rassert, rassume) = trans_annos ctx rest
          val (wf,chk,_,asm,_) = trans_assert (inRegion ctx ext) e
      in Anno(Seq[wf,rwf],Seq[chk, asm,rassert],Seq[asm,rassume]) end
      
fun trans_lhs ctx l = 
  case l of
     A.Var v => (Seq[], Local v)
   | A.Select(strct, f) => 
        let fun root ctx (A.OpExp(A.DEREF, [e])) = 
                    let val (edn,eup) = trans_expr_var ctx e
                    in (Seq[edn,deref_assert(var ctx eup, SOME(currentRegion ctx))], Cell eup) end
              | root ctx (A.Select(s, f)) =
                    let val (effects, lv) = root ctx s
                    in(effects, case lv of
                                   Cell p => let val Pointer(StructName sn) = tp_of (var ctx p)
                                             in Field(p, (sn,[f])) end
                                 | Field(ptr, (sn,fs)) => Field(ptr, (sn, f::fs)))
                    end
              | root ctx (A.Marked m) = root (inRegion ctx (Mark.ext m)) (Mark.data m)
        in root ctx l end
   | A.OpExp(A.SUB, [a, i]) =>
        let val (adn, aup) = trans_expr_var ctx a
            val (idn, iup) = trans_expr_var ctx i
        in (Seq[adn,idn], ArrayElem (aup,iup)) end
   | A.OpExp(A.DEREF, [p]) => 
        let val (pdn, pup) = trans_expr_var ctx p
        in (pdn, Cell pup) end
   | A.Marked m => trans_lhs (inRegion ctx (Mark.ext m)) (Mark.data m)
   | lhs => raise Fail ("Unrecognized LHS expression: " ^ Ast.Print.pp_exp lhs)
    
fun trans_stmt ctx s = 
  case s of
     A.Assign (operQ, lhs, rhs) =>
        let fun get_value (Local v) = var ctx v
              | get_value (Field (p,f)) = Make.select(Make.deref (var ctx p),f)
              | get_value (Cell p) = Make.deref (var ctx p)
              | get_value (ArrayElem(a,i)) = Make.sub(var ctx a,var ctx i)
            
            fun lcheck (Cell p) = deref_assert(var ctx p, regionOfExpr lhs)
              | lcheck _ = Seq[]
            
            val (ldn, lup) = trans_lhs ctx lhs
            val (edn, eup) = trans_expr_pure ctx rhs (infered_type ctx lhs)
            val (vdn, vup) =
              case operQ of
                 SOME originalOper =>
                   let val oper = trans_oper originalOper
                       val tp = tp_of eup
                       val lorig = freshVar ctx tp
                       val lexpr = Var(lorig, tp)
                   in (Seq[Assign(Local lorig, Expr (get_value lup)),
                           binop_assert oper (lexpr, eup)],
                       ValOp(oper, [lexpr, eup]))
                   end
               | NONE => (Seq[], eup)
        in
          Seq[ldn, edn, lcheck(lup), vdn, Assign(lup, Expr vup)]
        end
   | A.Exp e => let val (edn, eup) = trans_expr ctx e  (infered_type ctx e) in edn end
   | A.Seq ([], stmts) => Seq(map (trans_stmt ctx) stmts)
   | A.Seq (vdecls, stmts) =>
         trans_stmt ctx (A.Seq([],(map A.StmDecl vdecls)@stmts))
   | A.StmDecl (A.VarDecl(v,tp, SOME e, region)) =>
         trans_stmt ctx (A.Seq([A.VarDecl(v,tp,NONE,region)],
                               [A.Assign(NONE, A.Var v, e)]))
   | A.StmDecl (A.VarDecl(v,tp, NONE, region)) => (declareVar ctx (v, Make.make_tp tp); Seq [])
   | A.If (e, a, b) =>
         let val (edn, eup) = trans_expr_bool ctx e in 
           Seq[edn, If(eup, trans_stmt ctx a, trans_stmt ctx b)] end
   | A.While (e, invs, body) => 
         let val (edn, eup) = trans_expr_bool ctx e
             val body' = trans_stmt ctx body
             val label = newLabel()
             val _ = labelExt label (SOME (currentRegion ctx))
             val invExprs = (List.mapPartial (fn A.LoopInvariant d => SOME d
                                               | _ => NONE) invs)
         in
           Block(2,
             LabeledS(label, 
             While(edn, eup, trans_annos ctx invExprs,
               Block(1,body'))))
         end 
   | A.For _ => raise Fail "for's should have been elaborated already."
   | A.Continue => Break(1)
   | A.Break => Break(2)
   | A.Return (SOME e) =>
         let val (edn, eup) = trans_expr ctx e (returnType ctx) in
           case returnType ctx of 
           A.Bool => Seq[edn, If(eup, Seq[Assign(Local resultVar, Expr (ValOp(BoolConst true,[]))),Break(0)],
                                      Seq[Assign(Local resultVar, Expr (ValOp(BoolConst false,[]))),Break(0)])]
          | _ => Seq[edn, Assign(Local resultVar, Expr eup), Break(0)]
        end
   | A.Return NONE => Break(0)
   | A.Error _ => Assume(ValOp(BoolConst false,[]))
   | A.Assert (e, errors) => 
        Check(trans_annos ctx [(e, SOME(currentRegion ctx))])
   | A.Anno specs => 
        Check(trans_annos ctx (List.mapPartial
                                (fn A.Assertion d => SOME d | _ => NONE) specs))
   | A.Markeds mkd => 
       let val l = newLabel() 
           val _ = labelExt l (Mark.ext mkd)
       in LabeledS(l, trans_stmt (inRegion ctx (Mark.ext mkd)) (Mark.data mkd))
       end

fun trans_func (fdecl as A.Function(name, rtp, formals, SOME body, specs, false, region)) =
      let val rtp' = Make.make_tp rtp
          val (body', types) = Preprocess.preprocess false fdecl
          val table = Symbol.digest (SymMap.listItemsi (SymMap.insert(types, resultVar, rtp)))
          val ctx = (region, table, ref SymMap.empty, rtp):context
          val formals' = map (fn (A.VarDecl(s, tp, _,_)) =>
                                    (declareVar ctx (s, Make.make_tp tp);
                                    (s, Make.make_tp tp))) formals
          val body'' = Block(0, Make.simplify(trans_stmt ctx body'))
          fun simplifyAnnos (Anno (a,b,c)) = Anno (Make.simplify a, Make.simplify b, Make.simplify c)
          val locals = !(#3(ctx))
          val req = trans_annos ctx (List.mapPartial (fn A.Requires d => SOME d | _ => NONE) specs) 
          val ens = trans_annos ctx (List.mapPartial (fn A.Ensures d => SOME d | _ => NONE) specs)
      in Function(rtp', locals, formals', simplifyAnnos req, body'', simplifyAnnos ens) end
  | trans_func _ = raise Fail "Not a defined, internal function"
end
