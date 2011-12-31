(* Transforming the concrete C0 syntax into C0 control flow graphs *)
(* *)

signature MK_GRAPH = sig

  exception GraphConstruction 

  (* The boolean argument decides whether we "compile with assertions" *)
  val mkgraph : bool -> C0.stmt list -> CFG.graph
  val mkprog  : bool -> C0.prog -> CFG.prog

end

structure MkGraph :> MK_GRAPH = struct

  open CFG
  structure GA = GrowArray

  exception GraphConstruction 

  (* Internal state of the control flow graph construction, and operations *)
  datatype cfg_state 
    = X 
    | S of {break_pc : pc, continue_pc : pc, break_depth : int}

  fun push_scope X = X
    | push_scope (S {break_pc, continue_pc, break_depth}) = 
      S {break_pc = break_pc, 
         continue_pc = continue_pc,
         break_depth = break_depth + 1}

  fun push_loop _ (break_pc, continue_pc) = 
      S {break_pc = break_pc, continue_pc = continue_pc, break_depth = 0}

  fun get_break X = raise GraphConstruction
    | get_break (S data) = data

  type proto_graph = (pc option ref) node vector

  fun mkgraph anno stmts : graph =
    let
      val nodes : (pc option ref) node GA.growarray
        = GA.empty ()
          
      (* Emitting a node returns the new internal PC referring to that node *)
      fun emit node =
        let val pc = GA.length nodes in
          GA.update nodes pc node; 
          pc
        end

      (* process() takes a statement and an unitialized program counter. It
       * intializes the program counter, and returns a new program counter
       * that needs to be initialized. *)
      fun process_list (parent_next, []) cfg_state = parent_next
        | process_list (parent_next, stmt :: stmts) cfg_state = 
          process_list (process (parent_next, stmt) cfg_state, stmts) cfg_state

      and pop_a_lot (parent_next, n) =
        if n <= 0 then parent_next
        else let
          val next = ref NONE
          val this = emit (PopScope (next, n))
        in 
          parent_next := SOME this;
          next
        end

      and process (ref_start, stmt) cfg_state : pc option ref = 
        case stmt of
          C0.Decl (ty, var_name, NONE, pos) => 
          let 
            val ref_next = ref NONE
            val pc_stmt = emit (Declare (ty, var_name, ref_next))
          in
            ref_start := SOME pc_stmt;
            ref_next
          end
          
        | C0.Decl (ty, var_name, SOME e, pos) =>
          let 
            val ref_next = ref NONE
            val pc_assn = emit (Stmt (C0.Assign (C0.Var var_name, NONE, e),
                                      SOME pos, ref_next))
            val pc_decl = emit (Declare (ty, var_name, ref (SOME pc_assn)))
          in
            ref_start := SOME pc_decl;
            ref_next
          end

        | C0.Assert (pos, e1, e2) => 
          let 
            val ref_next = ref NONE
            val pc_stmt = emit (Assert (e1, e2, pos, ref_next))
          in
            ref_start := SOME pc_stmt;
            ref_next
          end

        | C0.SAssert (pos, e1) => 
          if not anno then ref_start else
          let 
            val ref_next = ref NONE
            val e2 = C0.Const (C0.String (Mark.show pos))
            val pc_stmt = emit (Assert (e1, e2, pos, ref_next))
          in
            ref_start := SOME pc_stmt;
            ref_next
          end

        | C0.Simp(stmt,pos) =>
          let 
            val ref_next = ref NONE
            val pc_stmt = emit (Stmt (stmt, SOME pos, ref_next))
          in 
            ref_start := SOME pc_stmt;
            ref_next
          end

        | C0.Return(exp, pos) =>
          let
            val pc_retn = emit (Return (exp, SOME pos))
          in
            ref_start := SOME pc_retn;
            ref NONE
          end

        | C0.Break pos =>
          let
            val {break_pc, break_depth, ...} = get_break cfg_state
            val ref_first = ref NONE
            val pc_start = emit (Stmt (C0.Noop, NONE, ref_first))
            val ref_last = pop_a_lot (ref_first, break_depth)
          in
            ref_start := SOME pc_start;
            ref_last := SOME break_pc;
            ref NONE
          end

        | C0.Continue pos =>
          let
            val {continue_pc, break_depth, ...} = get_break cfg_state
            val ref_first = ref NONE
            val pc_start = emit (Stmt (C0.Noop, SOME pos, ref_first))
            val ref_last = pop_a_lot (ref_first, break_depth)
          in
            ref_start := SOME pc_start;
            ref_last := SOME continue_pc;
            ref NONE
          end
    
        | C0.If (test, pos, stmtT, stmtF) =>
          let
            val ref_startT = ref NONE
            val ref_endT = process (ref_startT, stmtT) cfg_state

            val ref_startF = ref NONE
            val ref_endF =
                case stmtF of
                  NONE => ref_startF 
                | SOME stmtF => process (ref_startF, stmtF) cfg_state

            val pc_test = emit (Test (test, SOME pos, ref_startT, ref_startF))
            val ref_next = ref NONE
            val pc_final = emit (Stmt (C0.Noop, NONE, ref_next))

          in
            ref_start := SOME pc_test;
            ref_endT := SOME pc_final;
            ref_endF := SOME pc_final;
            ref_next
          end

        | C0.While (test, pos, spec, body) =>
          let
            val ref_next = ref NONE
            val pc_exit = emit (Stmt (C0.Noop, NONE, ref_next))

            val ref_beginbody = ref NONE
            val pc_test = 
                emit (Test (test, SOME pos, ref_beginbody, ref (SOME pc_exit)))

            val cfg_state = push_loop cfg_state (pc_exit, pc_test)
            val ref_endbody = process (ref_beginbody, body) cfg_state
          in
            ref_start := SOME pc_test;
            ref_endbody := SOME pc_test;
            ref_next
          end
            
        | C0.For((init, pinit), (test, ptest), (post, ppost), spec, body) =>
          let
            val ref_test = ref NONE
            val pc_init = emit (Stmt (init, SOME pinit, ref_test))

            val ref_next = ref NONE
            val pc_exit = emit (Stmt (C0.Noop, NONE, ref_next))

            val ref_beginbody = ref NONE
            val pc_test = 
             case test of 
               NONE => emit (Stmt (C0.Noop, SOME ptest, ref_beginbody))
             | SOME test =>
               emit (Test (test, SOME ptest, ref_beginbody, ref (SOME pc_exit)))

            val cfg_state = push_loop cfg_state (pc_exit, pc_test)
            val ref_endbody = process (ref_beginbody, body) cfg_state
            val pc_post = emit (Stmt (post, NONE, ref_test))
          in
            ref_start := SOME pc_init;
            ref_test := SOME pc_test;
            ref_endbody := SOME pc_post;
            ref_next
          end

        | C0.Compound (body) =>
          let
            val ref_beginbody = ref NONE
            val pc_start = emit (PushScope ref_beginbody)

            val cfg_state = push_scope cfg_state
            val ref_endbody = process_list (ref_beginbody, body) cfg_state

            val ref_next = ref NONE
            val pc_exit = emit (PopScope (ref_next, 1))
          in
            ref_start := SOME pc_start;
            ref_endbody := SOME pc_exit;
            ref_next
          end

      (* Create a fake entry point to push the initial scope. *)
      val ref_start : pc option ref = ref NONE
      val pc_entry : pc = emit (PushScope ref_start)
                                 
      (* Create the body of the function. *)
      val ref_end : pc option ref = process_list (ref_start, stmts) X

      (* Create a fake exit point in case there's no return statement. *)
      val pc_end : pc = emit (Return (NONE, NONE))
      val () = ref_end := SOME pc_end

      val mapper : pc option ref CFG.node -> pc CFG.node = 
        CFG.map (fn (ref NONE) => raise GraphConstruction
                  | (ref (SOME pc)) => pc)

      val graph = Vector.map mapper (Array.vector (GA.finalize nodes))

    in
      {entry_point = pc_entry, 
       nodes = graph}
    end

  fun mkprog_folder anno (decl, prog as {functions, ty_vars, struct_defs}) =
    case decl of
      C0.Extern _ => prog
    | C0.Fun _ => prog
    | C0.FunDef ((ty, f, args), spec, stmts) => 
      let 
        val function =
            CFG.Int {return_type = ty, args = args, graph = mkgraph anno stmts}
      in
        if MapS.inDomain (functions, f) then raise Error.Compilation
        else if MapS.inDomain (ty_vars, f) then raise Error.Compilation
        else
          {functions = MapS.insert (functions, f, function),
           ty_vars = ty_vars, 
           struct_defs = struct_defs}
      end
    | C0.Struct _ => prog
    | C0.StructDef (s, fields) => 
      let in
        {functions = functions,
         ty_vars = ty_vars,
         struct_defs = MapS.insert (struct_defs, s, fields)}
      end
    | C0.TypeDef (ty, t) => 
      let in
        if MapS.inDomain (functions, t) then raise Error.Compilation
        else
          {functions = functions,
           ty_vars = MapS.insert (ty_vars, t, ty),
           struct_defs = struct_defs}
      end

  (* XXX WE NEED TO EXPAND TYPES THROUGHOUT HERE *)
  val img_t = C0.TPointer (C0.TStruct "image")
  val file_t = C0.TPointer (C0.TStruct "file")

  val starting_point = 
   [("print",          C0.TUnit,          [ C0.TString ], "conio"),
    ("println",        C0.TUnit,          [ C0.TString ], "conio"),
    ("printint",       C0.TUnit,          [ C0.TInt ], "conio"),
    ("readline",       C0.TString,        [], "conio"),
    ("image_create",   img_t,             [ C0.TInt, C0.TInt ], "img"),
    ("image_clone",    img_t,             [ img_t ], "img"),
    ("image_destroy",  C0.TUnit,          [ img_t ], "img"),
    ("image_subimage", img_t,             [ img_t,          
                                            C0.TInt, C0.TInt, 
                                            C0.TInt, C0.TInt ], "img"),
    ("image_load",     img_t,             [ C0.TString ], "img"),
    ("image_save",     C0.TUnit,          [ img_t,           
                                            C0.TString ], "img"),
    ("image_width",    C0.TInt,           [ img_t ], "img"),
    ("image_height",   C0.TInt,           [ img_t ], "img"),
    ("image_data",     C0.TArray C0.TInt, [ img_t ], "img"),
    ("string_length",  C0.TInt,           [ C0.TString ], "string"),
    ("string_charat",  C0.TChar,          [ C0.TString, C0.TInt ], "string"),
    ("string_join",    C0.TString,        [ C0.TString, C0.TString ], "string"),
    ("string_sub",     C0.TString,        [ C0.TString, 
                                            C0.TInt, C0.TInt ], "string"),
    ("string_equal",   C0.TBool,          [ C0.TString, C0.TString ], "string"),
    ("string_compare", C0.TInt,           [ C0.TString, C0.TString ], "string"),
    ("char_equal",     C0.TBool,          [ C0.TChar, C0.TChar ], "string"),
    ("char_compare",   C0.TInt,           [ C0.TChar, C0.TChar ], "string"),
    ("string_frombool",C0.TString,        [ C0.TBool ], "string"),
    ("string_fromint", C0.TString,        [ C0.TInt ], "string"),
    ("file_read",      file_t,            [ C0.TString ], "file"),
    ("file_close",     C0.TUnit,          [ file_t ], "file"), 
    ("file_eof",       C0.TBool,          [ file_t ], "file"), 
    ("file_readline",  C0.TString,        [ file_t ], "file") ]
     
  fun proc_starting_point ((name, ty, args, lib), map) = 
      MapS.insert (map, name, Ext {return_type = ty, 
                                   args = args, 
                                   library = lib})

  val mkprog : bool -> C0.prog -> CFG.prog = 
   fn anno => 
      foldr (mkprog_folder anno)
            {functions = foldr proc_starting_point MapS.empty starting_point, 
             ty_vars = MapS.insert(
                           MapS.singleton ("image_t", img_t),
                           "file_t", file_t),
             struct_defs = MapS.empty}
      
end
