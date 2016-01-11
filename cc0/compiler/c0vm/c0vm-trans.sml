(* C0 Compiler
 * Code generation for c0vm
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature C0VM_TRANS =
sig

  (* trans arch_wsize program = bytecode *)
  val trans : int -> Ast.program -> C0VM.program

end (* signature C0VM_TRANS *)

signature C0VM_ARCH =
sig
    val sizeof : Ast.tp -> int (* sizeof tp, tp != struct s, typename *)
    val align : Ast.tp -> int  (* align tp, tp != struct s, typename *)
end

structure M32 :> C0VM_ARCH =
struct
  structure A = Ast

  (* sizeof tp = representation size, tp != struct s, typename *)
  fun sizeof (A.Int) = 4
    | sizeof (A.Bool) = 1
    | sizeof (A.String) = 4 (* address of string *)
    | sizeof (A.Char) = 1
    | sizeof (A.Pointer(t)) = 4
    | sizeof (A.Array(t)) = 4

  (* align tp = alignment requirement, tp != struct s, typename *)
  fun align (A.Int) = 4
    | align (A.Bool) = 1
    | align (A.String) = 4
    | align (A.Char) = 1
    | align (A.Pointer(t)) = 4
    | align (A.Array(t)) = 4

end

structure M64 :> C0VM_ARCH =
struct
  structure A = Ast

  (* sizeof tp = representation size, tp != struct s, typename *)
  fun sizeof (A.Int) = 4
    | sizeof (A.Bool) = 1
    | sizeof (A.String) = 8 (* address of string *)
    | sizeof (A.Char) = 1
    | sizeof (A.Pointer(t)) = 8
    | sizeof (A.Array(t)) = 8


  (* align tp = alignment requirement, tp != struct s, typename *)
  fun align (A.Int) = 4
    | align (A.Bool) = 1
    | align (A.String) = 4
    | align (A.Char) = 1
    | align (A.Pointer(t)) = 8
    | align (A.Array(t)) = 8

end

structure Arch :> sig
  val sizeof : int -> Ast.tp -> int
  val align : int -> Ast.tp -> int
end =
struct

  fun sizeof 32 tp = M32.sizeof tp
    | sizeof 64 tp = M64.sizeof tp
    | sizeof n tp = ( ErrorMsg.error NONE ("machine word size " ^ Int.toString n ^ " not implemented")
		    ; raise ErrorMsg.Error )

  fun align 32 tp = M32.align tp
    | align 64 tp = M64.sizeof tp
    | align n tp = ( ErrorMsg.error NONE ("machine word size " ^ Int.toString n ^ " not implemented")
		   ; raise ErrorMsg.Error )

end

structure Funtab = Symtab (type entrytp = int)
structure Nativetab = Symtab (type entrytp = int)
structure Structsizetab = Symtab (type entrytp = int * (Symbol.symbol * Ast.tp * int) list)

structure C0VMTrans :> C0VM_TRANS =
struct

  structure V = C0VM
  structure A = Ast

  type ext = Mark.ext option

  fun location (NONE) = "_"
    | location (SOME(mark)) = Mark.show(mark)

  fun nyi msg ext = ( ErrorMsg.error ext ("unimplemented feature: " ^ msg) ;
		      raise ErrorMsg.Error )

  val maxint16 = 65536
  val maxint15 = 32768
  val maxint8 = 256
  val maxint7 = 128

  fun get_fields_gdecl(SOME(A.Struct(_,SOME(fields),_,_))) = fields

  fun get_fields(s) = get_fields_gdecl (Structtab.lookup s)

  val wsize : int ref = ref 0

  fun align (A.StructName(s)) = align_fields 1 (get_fields s)
    | align (t as A.TypeName(aid)) = align (Syn.expand_def t)
    | align tp = Arch.align (!wsize) tp
  and align_fields n nil = n
    | align_fields n (A.Field(f, t, ext)::fields) =
        align_fields (Int.max(n, align(t))) fields

  fun sizeof (A.StructName(s)) = comp_size (Structtab.lookup s)
    | sizeof (t as A.TypeName(aid)) = sizeof (Syn.expand_def t)
    | sizeof tp = Arch.sizeof (!wsize) tp
  and comp_size (SOME(A.Struct(s, SOME(fields), library, ext))) =
      (case Structsizetab.lookup(s)
	of SOME(size, offsets) => size
	 | NONE => let val (raw_size, offsets) = comp_offsets (0, nil) fields
		       val salign = align(A.StructName(s))
		       val padded_size = (((raw_size-1) div salign)+1)*salign
		       val _ = Structsizetab.bind(s, (padded_size, offsets))
		   in
		       padded_size
		   end)
  and comp_offsets (n, offsets) nil = (n, offsets)
    | comp_offsets (n, offsets) (A.Field(f, t, ext)::fields) =
      let val fsize = sizeof(t)
	  val falign = align(t)
	  val foffset = (((n-1) div falign)+1)*falign
      in
	  comp_offsets (foffset+fsize, offsets @ [(f, t, foffset)]) fields
      end

  fun get_field_offset ((f', t, f'offset)::offsets) f =
      (case Symbol.compare(f, f')
	of EQUAL => f'offset
         | _ => get_field_offset offsets f)

  fun get_offset (A.StructName(s)) f ext =
      let val SOME(size, offsets) =
	      (case Structsizetab.lookup(s)
		of NONE => ( ignore(comp_size(Structtab.lookup(s)))
                           ; Structsizetab.lookup(s) )
		 | so => so)
	  val offset = get_field_offset offsets f
	  val _ = if offset >= maxint8
		  then ( ErrorMsg.error ext ("field offset too big")
		       ; raise ErrorMsg.Error )
		  else ()
      in
	  offset
      end

  fun pad2z(s) = if String.size(s) < 2
		then "0" ^ s
		else s

  local 
      val cindex = ref 0
      val sindex = ref 0
      val slength = ref 0
      val nindex = ref 0
      val num_vars = ref 0
      val findex = ref 1
      val glabel = ref 0
  in
      val int_pool = Array.array(maxint16, Word32.fromInt(0))
      fun next_cindex () =
	  let val i = !cindex
	      val _ = if !cindex >= maxint16
		      then ( ErrorMsg.error NONE ("too many constants") ;
			     raise ErrorMsg.Error )
		      else ()
	      val _ = ( cindex := !cindex+1 )
	  in
	      i
	  end
      val string_pool = Array.array(maxint16, "")
      fun next_sindex () =
	  let val i = !sindex
	      val _ = if !sindex >= maxint16
		      then ( ErrorMsg.error NONE ("too many strings") ;
			     raise ErrorMsg.Error )
		      else ()
	      val _ = ( sindex := !sindex+1 )
	  in
	      i
	  end
      fun inc_slength (n) = ( slength := !slength+n )
      fun get_slength () = !slength

      val function_pool : V.function_info option array = Array.array(maxint16, NONE)
      fun track_num_vars(vlist) =
	  if List.length(vlist) > !num_vars
	  then num_vars := List.length(vlist)
	  else ()
      fun get_num_vars() = !num_vars
      fun next_findex() =
	  let val i = !findex
	      val _ = if !findex >= maxint16
		      then ( ErrorMsg.error NONE ("too many functions") ;
			     raise ErrorMsg.Error )
		      else ()
	      val _ = ( findex := !findex+1 )
	  in
	      i
	  end

      val label_map = Array.array(maxint16, 0)
      fun next_glabel(s) =
	  let val lab = (!glabel, "<" ^ pad2z(Int.toString(!glabel)) ^ ":" ^ s ^ ">")
	      val _ = ( glabel := !glabel+1 )
	  in
	      lab
	  end
      fun num_labels() = !glabel

      val native_pool = ref (nil:V.native_info list)
      fun new_native(g, num_args, ext) =
	  let val n = !nindex
	      val ntindex = C0VMNative.native_index(Symbol.name(g))
	      val _ = if ntindex < 0 orelse ntindex >= maxint16 orelse
                   n < 0 orelse n >= maxint16
		      then ( ErrorMsg.error ext ("unsupported native function " ^ Symbol.name(g)) ;
			     raise ErrorMsg.Error )
		      else ()
	      val ni = V.NI { name = Symbol.name(g),
			      num_args = num_args,
			      function_table_index = ntindex }
	      val _ = ( native_pool := !native_pool @ [ni] )
	      val _ = ( nindex := n+1 )
	      val _ = Nativetab.bind(g, n)
	  in
	      n
	  end
      fun native_index(g, ext) =
	  (case (Nativetab.lookup(g), Symtab.lookup(g))
            of (SOME(c), _) => c (* native function seen before *)
	     | (NONE, SOME(A.Function(g', rtp, params, NONE, specs, true, ext'))) =>
	       (* new native function *)
	       new_native(g, length(params), ext)
            | (NONE, SOME(A.Function(g', rtp, params, _, specs, _, ext'))) =>
	      (* intermediary, due to dynamic assertion checking *)
	      (* hack alert!! ignoring wrapper!! *)
	      new_native(g, length(params), ext)
            | (NONE, NONE) =>
	      case Symbol.name(g)
	       of "string_join" => new_native(g, 2, ext)
		| _ => ( ErrorMsg.error ext ("undefined function " ^ Symbol.name(g))
		       ; raise ErrorMsg.Error ))

      fun reset () =
	  ( cindex := 0 ;
	    num_vars := 0 ;
	    findex := 1 ;
	    sindex := 0 ;
	    slength := 0 ;
	    nindex := 0 ;
	    native_pool := nil ;
	    glabel := 0 ;
	    Funtab.reset() ;
            Funtab.bind(Symbol.symbol "main", 0) ;
	    Nativetab.reset() ;
	    Structsizetab.reset()
	  )
  end

  fun labToString (n, lab) = lab

  (* labMap n insts
   * populates the global label map label_map
   * with the address in bytes, counting from the
   * beginning of the function where it occurs *)
  fun labMap n (nil) = ()
    | labMap n (V.Label(k, _)::is) =
      ( Array.update(label_map, k, n)
      ; labMap n is )
    | labMap n (V.Comment _ :: is) =
        labMap n is
    | labMap n (V.Inst(inst,_,_)::is) =
        labMap (n + V.il(inst)) is

  (* labToOffsets n insts accum = insts'
   * replaces the label number in each conditional branch
   * with the correct offset, based on the global label map *)
  fun labToOffsets n (nil) accum = List.rev accum
    | labToOffsets n ((l as V.Label _)::is) accum =
        labToOffsets n is (l::accum)
    | labToOffsets n ((c as V.Comment _)::is) accum =
        labToOffsets n is (c::accum)
    | labToOffsets n (V.Inst(inst as V.if_cmp(cmp, (k, sym)), anno, ext)::is) accum =
      let val offset = Array.sub(label_map, k) - n
      in
          labToOffsets (n + V.il(inst)) is
          (V.Inst(V.if_cmp(cmp, (offset, sym)), anno, ext)::accum)
      end
    | labToOffsets n (V.Inst(inst as V.goto(k,sym), anno, ext)::is) accum =
      let val offset = Array.sub(label_map, k) - n
      in
          labToOffsets (n + V.il(inst)) is
          (V.Inst(V.goto(offset, sym), anno, ext)::accum)
      end
    | labToOffsets n ((i as V.Inst(inst, anno, ext))::is) accum =
      labToOffsets (n + V.il(inst)) is (i::accum)

  val string_join = Symbol.symbol "string_join"
  fun join (e1::nil) = e1
    | join (e1::e2s) = A.FunCall(string_join, [e1,join e2s])

  fun tbinop A.TIMES = V.imul
    | tbinop A.DIVIDEDBY = V.idiv
    | tbinop A.MODULO = V.irem
    | tbinop A.PLUS = V.iadd
    | tbinop A.MINUS = V.isub
    | tbinop A.SHIFTLEFT = V.ishl
    | tbinop A.SHIFTRIGHT = V.ishr
    | tbinop A.AND = V.iand
    | tbinop A.XOR = V.ixor
    | tbinop A.OR = V.ior

  fun isrel A.LESS = true
    | isrel A.LEQ = true
    | isrel A.GREATER = true
    | isrel A.GEQ = true
    | isrel A.EQ = true
    | isrel A.NOTEQ = true
    | isrel _ = false

  fun trel A.LESS = V.lt
    | trel A.LEQ = V.le
    | trel A.GREATER = V.gt
    | trel A.GEQ = V.ge
    | trel A.EQ = V.eq
    | trel A.NOTEQ = V.ne

  fun get_const (A.IntConst(w)) = SOME(w)
    | get_const (A.Marked(marked_exp)) =
        get_const (Mark.data marked_exp)
    | get_const _ = NONE

  fun lookup (A.VarDecl(y, t, e_opt, ext)::vlist) i x =
      case Symbol.compare(x,y)
        of EQUAL => if i < 0 orelse i >= maxint8
                    then ( ErrorMsg.error NONE ("too many variables") ;
                          raise ErrorMsg.Error )
                    else i
         | _ => lookup vlist (i+1) x

  fun trans_exp env vlist (A.Var(x)) ext =
      let val vindex = lookup vlist 0 x
      in
          [V.Inst(V.vload(vindex), Symbol.name(x), ext)]
      end
    | trans_exp env vlist (A.IntConst(w)) ext =
      (* include small integers -128 <= w < 128 directly in 
       * instruction stream using bipush instruction; slightly
       * tricky to avoid overflow *)
      if Word32.<(w, Word32.fromInt(maxint7))
      then [V.Inst(V.bipush(Word32.toInt(w)), Word32Signed.toString(w), ext)]
      else if Word32.<=(Word32.~(w), Word32.fromInt(maxint7))
      then [V.Inst(V.bipush(~(Word32.toInt(Word32.~(w)))), Word32Signed.toString(w), ext)]
      else let val i = next_cindex()
               val _ = Array.update(int_pool, i, w)
           in 
               [V.Inst(V.ildc(i), "c[" ^ Int.toString(i) ^ "] = "
                                  ^ Word32Signed.toString(w), ext)]
           end
    | trans_exp env vlist (A.StringConst(s)) ext =
      let val i = next_sindex()
          val spos = get_slength()
          val _ = inc_slength(String.size(s)+1) (* add 1 for '\0' char *)
          val _ = Array.update(string_pool, i, s)
      in
          [V.Inst(V.aldc(spos),
                  "s[" ^ Int.toString(spos) ^ "] = \"" ^ String.toCString(s) ^ "\"",
                  ext)]
      end 
    | trans_exp env vlist (A.CharConst(c)) ext =
      (* 0 <= ord(c) < 128 *)
      let val i = Char.ord(c)
          val _  = (if i < 0 orelse i >= maxint7
                   then ( ErrorMsg.error NONE ("Illegal char constant") ;
                          raise ErrorMsg.Error )
                   else ())
      in 
        [V.Inst(V.bipush(i), "'" ^ Char.toCString c ^ "'", ext)]
      end
    | trans_exp env vlist (A.True) ext =
      [V.Inst(V.bipush(1), "true", ext)]
    | trans_exp env vlist (A.False) ext =
      [V.Inst(V.bipush(0), "false", ext)]
    | trans_exp env vlist (A.Null) ext =
      [V.Inst(V.aconst_null, "NULL", ext)]
    | trans_exp env vlist (e as A.OpExp(A.DEREF, [e1])) ext =
      let val is1 = trans_exp env vlist e1 ext
          val size = sizeof(Syn.syn_exp_expd env e)
          val load_inst = (case size of 1 => V.cmload | 4 => V.imload | 8 => V.amload)
      in
          is1 @ [V.Inst(load_inst, A.Print.pp_exp(e), ext)]
      end
    | trans_exp env vlist (e as A.OpExp(A.SUB, [lv1,e2])) ext =
      let val is1 = trans_exp env vlist lv1 ext
          val is2 = trans_exp env vlist e2 ext
          val size = sizeof(Syn.syn_exp_expd env e)
          val load_inst = (case size of 1 => V.cmload | 4 => V.imload | 8 => V.amload)
      in
          is1 @ is2
          @ [V.Inst(V.aadds, "&" ^ A.Print.pp_exp(e), ext),
             V.Inst(load_inst, A.Print.pp_exp(e), ext)]
      end
    | trans_exp env vlist (e as A.OpExp(A.LOGNOT, [e1])) ext =
      trans_exp env vlist e1 ext
      @ [V.Inst(V.bipush(1), "", ext)]
      @ [V.Inst(V.binop(V.ixor), A.Print.pp_exp(e), ext)]
    | trans_exp env vlist (e as A.OpExp(A.COMPLEMENT, [e1])) ext =
      trans_exp env vlist e1 ext
      @ [V.Inst(V.bipush(~1), "", ext)]
      @ [V.Inst(V.binop(V.ixor), A.Print.pp_exp(e), ext)]
    | trans_exp env vlist (e as A.OpExp(A.NEGATIVE, [e1])) ext =
      (* try constant folding for -<n> in order to include small
       * negative integer constants in the instruction stream *)
      (case get_const(e1)
        of SOME(w) => trans_exp env vlist (A.IntConst(Word32.~(w))) ext
         | NONE => [V.Inst(V.bipush(0), "", ext)]
                   @ trans_exp env vlist e1 ext
                   @ [V.Inst(V.binop(V.isub), A.Print.pp_exp(e), ext)])
    | trans_exp env vlist (A.OpExp(A.LOGAND, [e1, e2])) ext =
        trans_exp env vlist (A.OpExp(A.COND, [e1, e2, A.False])) ext (* fix? *)
    | trans_exp env vlist (A.OpExp(A.LOGOR, [e1, e2])) ext =
        trans_exp env vlist (A.OpExp(A.COND, [e1, A.True, e2])) ext (* fix? *)
    | trans_exp env vlist (A.OpExp(A.COND, [e1, e2, e3])) ext =
      let val true_lab = next_glabel("cond_true")
          val false_lab = next_glabel("cond_false")
          val end_lab = next_glabel("cond_end")
          val is1 = trans_cond env vlist e1 true_lab false_lab ext
          val is2 = trans_exp env vlist e2 ext
          val is3 = trans_exp env vlist e3 ext
      in
          is1
          @ [V.Label(true_lab)] @ is2
          @ [V.Inst(V.goto(end_lab), "goto " ^ labToString end_lab, ext)]
          @ [V.Label(false_lab)] @ is3 (* @ V.goto(end_lab) is unecessary *)
          @ [V.Label(end_lab)]
      end
    | trans_exp env vlist (e as A.OpExp(opr, [e1, e2])) ext =
      if isrel opr              (* hopefully this will not lead to an inf. loop *)
      then trans_exp env vlist (A.OpExp(A.COND, [e, A.True, A.False])) ext
      else let val is1 = trans_exp env vlist e1 ext
               val is2 = trans_exp env vlist e2 ext
           in
               is1 @ is2 @ [V.Inst(V.binop(tbinop(opr)), A.Print.pp_exp e, ext)]
           end
    | trans_exp env vlist (e as A.Select(lv1, f)) ext =
      let val is1 = trans_lv env vlist lv1 ext (* computes address *)
          val t1 = Syn.syn_exp_expd env lv1
          val foffset = get_offset t1 f ext
          val data_size = sizeof(Syn.syn_exp_expd env e)
          val load_inst = (case data_size of 1 => V.cmload | 4 => V.imload | 8 => V.amload)
      in
          is1                        (* compute address *)
          @ [V.Inst(V.aaddf(foffset), "&" ^ A.Print.pp_exp e, ext)]
          @ [V.Inst(load_inst, A.Print.pp_exp e, ext)]
      end 
    | trans_exp env vlist (e as A.FunCall(g, es)) ext =
      (case Funtab.lookup(g)
        of SOME(c) => let val _ = if c >= maxint16
                                  then ( ErrorMsg.error NONE ("static function index too big") ;
                                         raise ErrorMsg.Error )
                                  else ()
                      in trans_exps env vlist es ext
                         @ [V.Inst(V.invokestatic(c),
                            A.Print.pp_exp(e), ext)]
                      end
         | NONE => (* should be native (library) function *)
           (let
                val c = native_index(g, ext)
            in
                trans_exps env vlist es ext
                @ [V.Inst(V.invokenative(c), A.Print.pp_exp(e), ext)]
            end))
    | trans_exp env vlist (e as A.Alloc(t)) ext =
      let val size = sizeof(t)
              (* Overflow should be impossible here, since it would have been caught earlier *)
              (* handle Overflow => ( ErrorMsg.error ext ("newarray: array elements way too big")
                                                  ; raise ErrorMsg.Error ) *)
          val _  = (if size < 0 orelse size >= maxint8
                   then ( ErrorMsg.error ext ("new: struct too big") ;
                          raise ErrorMsg.Error )
                   else ())
      in [V.Inst(V.new(size), A.Print.pp_exp(e), ext)]
      end
    | trans_exp env vlist (e as A.AllocArray(t, e1)) ext =
      let val size = sizeof(t)  (* size check necessary? *)
          val _  = (if size < 0 orelse size >= maxint8
                    then ( ErrorMsg.error NONE ("newarray: array elements too big") ;
                           raise ErrorMsg.Error )
                    else ())
      in trans_exp env vlist e1 ext
         @ [V.Inst(V.newarray(size), A.Print.pp_exp(e), ext)]
      end
    | trans_exp env vlist (e as A.Cast(t, e1)) ext =
      ( ErrorMsg.error NONE ("cast not supported by c0vm") ;
        raise ErrorMsg.Error )
    | trans_exp env vlist (e as A.Length(e1)) ext =
        trans_exp env vlist e1 ext
        @ [V.Inst(V.arraylength, A.Print.pp_exp(e), ext)]
    | trans_exp env vlist (A.Marked(marked_exp)) ext = 
        trans_exp env vlist (Mark.data marked_exp) (Mark.ext marked_exp) 
    (* these two should be impossible here *)
    (*
    | trans_exp env vlist (A.Result) ext = nyi "Result" ext
    | trans_exp env vlist (A.Old(e)) ext = nyi "Old" ext
    *)
  and trans_exps env vlist nil ext = []
    | trans_exps env vlist (e::es) ext =
        trans_exp env vlist e ext
        @ trans_exps env vlist es ext
  and trans_lv env vlist (A.OpExp(A.DEREF, [lv1])) ext =
        trans_exp env vlist lv1 ext        (* lv1 computes address *)
    | trans_lv env vlist (lv as A.OpExp(A.SUB, [lv1, e2])) ext =
      let val is1 = trans_exp env vlist lv1 ext (* lv1 computes address *)
          val is2 = trans_exp env vlist e2 ext
      in
          is1 @ is2
          @ [V.Inst(V.aadds, "&" ^ A.Print.pp_exp(lv), ext)]
      end
    | trans_lv env vlist (e as A.Select(lv1, f)) ext =
      let val is1 = trans_lv env vlist lv1 ext
          val t1 = Syn.syn_exp_expd env lv1
          val foffset = get_offset t1 f ext
      in
          is1 @ [V.Inst(V.aaddf(foffset), "&" ^ A.Print.pp_exp e, ext)]
      end
    | trans_lv env vlist (A.Marked(marked_exp)) ext =
        trans_lv env vlist (Mark.data marked_exp) (Mark.ext marked_exp)

  (* trans_cond env vlist e then_lab else_lab ext = is
   * Executing 'is' evaluates e : bool.
   * If true, it jumps to then_lab.
   * If false, it jumps to else_lab.
   *)
  and trans_cond env vlist (A.Marked(marked_exp)) then_lab else_lab ext =
        trans_cond env vlist (Mark.data marked_exp) then_lab else_lab (Mark.ext marked_exp)
    | trans_cond env vlist (e as A.OpExp(opr, [e1, e2])) then_lab else_lab ext =
      if isrel opr
      then let val is1 = trans_exp env vlist e1 ext
               val is2 = trans_exp env vlist e2 ext
               val anno = A.Print.pp_exp e
           in
               is1 @ is2
               @ [V.Inst(V.if_cmp(trel(opr), then_lab),
                         "if " ^ anno ^ " goto " ^ labToString(then_lab), ext),
                  V.Inst(V.goto(else_lab),
                         "goto " ^ labToString(else_lab), ext)]
           end
      else trans_cond' env vlist e then_lab else_lab ext
    | trans_cond env vlist e then_lab else_lab ext =
        trans_cond' env vlist e then_lab else_lab ext
  and trans_cond' env vlist (A.OpExp(A.LOGNOT, [e1])) then_lab else_lab ext =
        trans_cond env vlist e1 else_lab then_lab ext
    | trans_cond' env vlist (A.OpExp(A.LOGAND, [e1, e2])) then_lab else_lab ext =
      let val newlabel = next_glabel("and")
      in
          trans_cond env vlist e1 newlabel else_lab ext
          @ [V.Label(newlabel)]
          @ trans_cond env vlist e2 then_lab else_lab ext
      end
    | trans_cond' env vlist (e as A.OpExp(A.LOGOR, [e1, e2])) then_lab else_lab ext =
      let val newlabel = next_glabel("or")
      in
          trans_cond env vlist e1 then_lab newlabel ext
          @ [V.Label(newlabel)]
          @ trans_cond env vlist e2 then_lab else_lab ext
      end
    | trans_cond' env vlist (e as A.OpExp(A.COND, [e1, e2, e3])) then_lab else_lab ext =
      let val newlabel2 = next_glabel("cond_true")
          val newlabel3 = next_glabel("cond_false")
      in
          trans_cond env vlist e1 newlabel2 newlabel3 ext
          @ [V.Label(newlabel2)] @ trans_cond env vlist e2 then_lab else_lab ext
          @ [V.Label(newlabel3)] @ trans_cond env vlist e3 then_lab else_lab ext
      end
    | trans_cond' env vlist (A.True) then_lab else_lab ext =
      [V.Inst(V.goto(then_lab), "goto " ^ labToString(then_lab), ext)]
    | trans_cond' env vlist (A.False) then_lab else_lab ext =
      [V.Inst(V.goto(else_lab), "goto " ^ labToString(else_lab), ext)]
    | trans_cond' env vlist e then_lab else_lab ext =
      (* all other case: translate as expressions and compare result to 'true' *)
      let val is = trans_exp env vlist e ext
      in is @ [V.Inst(V.bipush(1), "true", ext),
               V.Inst(V.if_cmp(V.eq, then_lab),
                      "if (" ^ A.Print.pp_exp e ^ " == true) goto " ^ labToString(then_lab), ext),
               V.Inst(V.goto(else_lab),
                      "goto " ^ labToString(else_lab), ext)]
      end

  fun trans_stm env vlist (A.Assign(oper_opt, l1, e2)) conts breaks ext =
        trans_assign env vlist oper_opt l1 e2 ext
    | trans_stm env vlist (A.Exp(e)) conts breaks ext =
        trans_exp env vlist e ext
        @ [V.Inst(V.pop, "(ignore result)", ext)]
    | trans_stm env vlist (A.Seq(ds, ss)) conts breaks ext = 
        trans_seq env vlist ds ss conts breaks ext
    | trans_stm env vlist (A.StmDecl(d)) conts breaks ext = (* empty scope *)
        trans_seq env vlist [d] [] conts breaks ext
    | trans_stm env vlist (A.If(e1, s2, s3)) conts breaks ext =
      let val then_lab = next_glabel("then")
          val else_lab = next_glabel("else")
          val endif_lab = next_glabel("endif")
          val is1 = trans_cond env vlist e1 then_lab else_lab ext
          val is2 = trans_stm env vlist s2 conts breaks ext
          val is3 = trans_stm env vlist s3 conts breaks ext
      in
          is1
          @ [V.Label(then_lab)] @ is2
          @ [V.Inst(V.goto(endif_lab), "goto " ^ labToString endif_lab, ext)]
          @ [V.Label(else_lab)] @ is3 (* @ V.goto(endif_lab) is unnecessary *)
          @ [V.Label(endif_lab)]
      end
    | trans_stm env vlist (A.While(e1, _, s2)) conts breaks ext = (* ignore invariants *)
      let val loop_lab = next_glabel("loop")
          val body_lab = next_glabel("body")
          val exit_lab = next_glabel("exit")
          val is1 = trans_cond env vlist e1 body_lab exit_lab ext
          val is2 = trans_stm env vlist s2 (loop_lab::conts) (exit_lab::breaks) ext
      in
          [V.Label(loop_lab)]
          @ is1
          @ [V.Label(body_lab)]
          @ is2
          @ [V.Inst(V.goto(loop_lab), "goto " ^ labToString(loop_lab), ext)]
          @ [V.Label(exit_lab)]
      end 
    (* no A.For *)
    | trans_stm env vlist (A.Continue) (loop_lab::conts) breaks ext =
        [V.Inst(V.goto(loop_lab), "continue", ext)]
    | trans_stm env vlist (A.Break) conts (exit_lab::breaks) ext =
        [V.Inst(V.goto(exit_lab), "break", ext)]
    | trans_stm env vlist (A.Return(NONE)) conts breaks ext =
        [V.Inst(V.bipush(0),"dummy return value", ext),
         V.Inst(V.return, "", ext)]
    | trans_stm env vlist (A.Return(SOME(e))) conts breaks ext =
        trans_exp env vlist e ext
        @ [V.Inst(V.return, "", ext)]
    | trans_stm env vlist (A.Assert(e1, e2s)) conts breaks ext =
      let val e2 = case e2s
                    of [] => A.StringConst(location ext ^ ": assertion failed")
                     | e2s => join e2s
      in
        trans_exp env vlist e1 ext
        @ trans_exp env vlist e2 ext
        @ [V.Inst(V.assert, 
                  "assert" ^ A.Print.pp_exp(e1) 
                  ^ " [failure message on stack]", (* ^ A.Print.pp_exp(e2) *)
                  ext)]
      end
    | trans_stm env vlist (A.Error(e)) conts breaks ext = 
        trans_exp env vlist e ext
        @ [V.Inst(V.athrow, "error " ^ A.Print.pp_exp(e), ext)]
    | trans_stm env vlist (A.Anno(specs)) conts breaks ext =
      (* ignore annotations; handled in ../type/dyn-check.sml *)
      []
    | trans_stm env vlist (A.Markeds(marked_stm)) conts breaks ext =
        trans_stm env vlist (Mark.data marked_stm) conts breaks (Mark.ext marked_stm)
  and trans_seq env vlist nil ss conts breaks ext =
      ( track_num_vars(vlist) ;
        trans_stms env vlist ss conts breaks ext )
    | trans_seq env vlist ((d as A.VarDecl(x,t,NONE,_))::ds) ss conts breaks ext =
        trans_seq (Symbol.bind env (x,t)) (vlist @ [d]) ds ss conts breaks ext
    | trans_seq env vlist ((d as A.VarDecl(x,t,SOME(e),ext'))::ds) ss conts breaks ext =
      let val vlist' = vlist @ [d]
          val env' = Symbol.bind env (x, t)
      in
          trans_exp env vlist e ext'
          @ [V.Inst(V.vstore (lookup vlist' 0 x),
                    A.Print.pp_stm(A.Assign(NONE, A.Var(x), e)),
                    ext')]
          @ trans_seq env' vlist' ds ss conts breaks ext
      end
  and trans_stms env vlist nil conts breaks ext = []
    | trans_stms env vlist (s::ss) conts breaks ext =
        trans_stm env vlist s conts breaks ext
        @ trans_stms env vlist ss conts breaks ext

  and trans_assign env vlist NONE (A.Var(x)) e ext = 
        trans_exp env vlist e ext
        @ [V.Inst(V.vstore(lookup vlist 0 x),
                  A.Print.pp_stm(A.Assign(NONE, A.Var(x), e)),
                  ext)]
    | trans_assign env vlist (SOME(opr)) (A.Var(x)) e ext =
        [V.Inst(V.vload(lookup vlist 0 x), Symbol.name(x), ext)]
        @ trans_exp env vlist e ext
        @ [V.Inst(V.binop(tbinop(opr)), "", ext)]
        @ [V.Inst(V.vstore(lookup vlist 0 x),
                  A.Print.pp_stm(A.Assign(SOME(opr), A.Var(x), e)),
                  ext)]
    | trans_assign env vlist oper_opt (A.Marked(marked_exp)) e ext =
        trans_assign env vlist oper_opt (Mark.data marked_exp) e (Mark.ext marked_exp)
    | trans_assign env vlist (NONE) lv1 e2 ext =
      let val is1 = trans_lv env vlist lv1 ext (* computes address of lv, not value! *)
          val is2 = trans_exp env vlist e2 ext
          val size = sizeof(Syn.syn_exp_expd env lv1)
          val store_inst = (case size of 1 => V.cmstore | 4 => V.imstore | 8 => V.amstore)
      in
          is1 @ is2
          @ [V.Inst(store_inst, A.Print.pp_stm(A.Assign(NONE, lv1, e2)), ext)]
      end 
    | trans_assign env vlist (SOME(opr)) lv1 e2 ext =
      let val is1 = trans_lv env vlist lv1 ext (* computes address of lv, not value! *)
          val is2 = trans_exp env vlist e2 ext
          val size = sizeof(Syn.syn_exp_expd env lv1)
          val load_inst = (case size of 1 => V.cmload | 4 => V.imload | 8 => V.amload)
          val store_inst = (case size of 1 => V.cmstore | 4 => V.imstore | 8 => V.amstore)
      in
          is1
          @ [V.Inst(V.dup, "(save &" ^ A.Print.pp_exp(lv1) ^ ")", ext)]
          @ [V.Inst(load_inst, A.Print.pp_exp(lv1), ext)]
          @ is2
          @ [V.Inst(V.binop(tbinop(opr)), "", ext)]
          @ [V.Inst(store_inst, A.Print.pp_stm(A.Assign(SOME(opr), lv1, e2)), ext)]
      end 

  fun trans_gdecl (A.Function(g, rtp, params, SOME(body), specs, is_external, ext)) =
      (* is_external = false ? perhaps not for C0 libraries like <rand> *)
      (* function definition *)
      let val findex = ( case Funtab.lookup(g)
                          of NONE => next_findex()
                           | SOME(findex) => findex )
          val _ = Funtab.bind(g, findex)
(*
          val _ = print((if is_external then "External" else "Internal")
                        ^ "Def: " ^ Symbol.name(g) ^ "\n")
*)
          val num_args = length(params)
          val _ = track_num_vars(params)
          val _  = (if num_args < 0 orelse num_args >= maxint16
                   then ( ErrorMsg.error NONE ("too many arguments of function: " ^ (Symbol.name g)) ;
                          raise ErrorMsg.Error )
                   else ())
          (* make possibly implicit return explicit for functions returning void *)
          val body' = (case Syn.expand_def(rtp)
                       of A.Void => A.Seq([], [body, A.Return(NONE)])
                          | _ => body)
          val env0 = Syn.syn_decls Symbol.empty params
          val is = trans_stm env0 params body' nil nil ext
          val num_vars = get_num_vars()
          val _  = (if num_vars < 0 orelse num_vars >= maxint16
                   then ( ErrorMsg.error NONE ("too many variables in function: " ^ (Symbol.name g)) ;
                          raise ErrorMsg.Error )
                   else ())
          val _ = labMap 0 is   (* compute mapping from labels to addresses *)
          val is' = labToOffsets 0 is nil (* replace labels by offsets *)
          val code_length = V.code_length(is')
          val _  = (if code_length < 0 orelse code_length >= maxint16
                   then ( ErrorMsg.error NONE ("body of function: " ^ (Symbol.name g) ^ "too long") ;
                          raise ErrorMsg.Error )
                   else ())
          val fi = V.FI {name = Symbol.name(g),
                         num_args = num_args, num_vars = num_vars,
                         code_length = code_length, code = is'}
          val _ = Array.update(function_pool, findex, SOME(fi))
      in
          ()
      end
    | trans_gdecl (A.Function(g, rtp, params, NONE, specs, false, ext)) =
      (* is_external = false *)
      (* assign index for forward declaration of non-library function *)
      (* this decl, and any previous decl must be non-library (false) *)
      ( case (Funtab.lookup(g), Symtab.lookup(g))
               of (NONE, SOME(A.Function(g', rtp', params', bodyOpt', specs', false, ext')))
            (* is_external = true allowed in spring'11 revision *)
            => let val findex = next_findex() (* "main" not possible since seeded in Funtab *)
                   (* val _ = print("Internal Decl:" ^ Symbol.name(g) ^ "\n") *)
                   val _ = Funtab.bind(g, findex)
                   val _ = Array.update(function_pool, findex, NONE)
               in 
                   ()
               end
          | (_, _) => ((* print("Internal Decl (ign): " ^ Symbol.name(g) ^ "\n") *)) )
    | trans_gdecl (A.Function(g, rtp, params, NONE, specs, true, ext)) =
      (* ignore declarations in libraries *)
      ((* print("External Decl (ign): " ^ Symbol.name(g) ^ "\n") *))
    | trans_gdecl (A.TypeDef(a,t,ext)) =
        ()                        (* ignore typedef *)
    | trans_gdecl (A.Struct(s, NONE, library, ext)) =
        ()                        (* ignore struct declaration *)
    | trans_gdecl (gdecl as A.Struct(s, SOME(fields), library, ext)) =
      (* struct s; compute and store field offsets, check max size *)
      let val size = comp_size (SOME(gdecl))
                     handle Overflow => ( ErrorMsg.error ext ("struct way too big")
                                        ; raise ErrorMsg.Error )
          val () = if size >= maxint8
                   then ( ErrorMsg.error ext ("struct size " ^ Int.toString size ^ " too big")
                        ; raise ErrorMsg.Error )
                   else ()
      in
          ()
      end
    | trans_gdecl (gdecl as A.Pragma(A.Raw(pname, pargs), ext)) =
      ()
    | trans_gdecl (A.Pragma(A.UseFile(filename, SOME(decls)), ext)) =
        trans_gdecls decls
    | trans_gdecl (A.Pragma(A.UseLib(libname, SOME(decls)), ext)) =
        trans_gdecls decls
    | trans_gdecl (gdecl as A.Pragma(p, ext)) =
      (* Ignore pragmas at this point?? *)
      ()

  and trans_gdecls nil = ()
    | trans_gdecls (gdecl::gdecls) =
        ( trans_gdecl gdecl ; trans_gdecls gdecls )

  fun trans arch_wsize gdecls =
      let val () = reset()  (* reset pools, struct size tab *)
	  val () = ( wsize := arch_wsize )
	  val () = trans_gdecls gdecls   (* also initialize Funtab, function pool *)
      in
	  V.BC0File { int_pool = (next_cindex(), int_pool),
		      string_pool = (next_sindex(), get_slength(), string_pool),
		      function_pool = (next_findex(), function_pool),
		      native_pool = !native_pool }
      end

end (* structure C0VMTrans *)
