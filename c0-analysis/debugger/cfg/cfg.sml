(* Control flow graph for C0 programs *)
(* Robert J. Simmons                  *)

(* 
Control flow graphs are an alternative to the "C0 statements" 
portion of the C0 grammar, but they rely on the "C0 expressions" as defined in 
lang/sources.cm. They are a particular intermediate form of programs that it 
is designed with the Cymbol interpreter (and the DASH program analysis 
algorithm it may eventually support) in mind. 

Nodes are parametric in the type of the abstract, internal program counters;
this isn't a terribly important feature, but it makes certain parts of the 
graph construction algorithm simpler. 

Right now, we expose the representation of graphs - internal program counters
are integers that index into a vector of (node, external_pc) pairs. It might
be worth changing around the interface to make internal program counters
abstract and have a similarly abstract "look up node in graph given an
internal program counter" function.
*)

structure CFG = struct

  type pc = int
  type pos = C0.pos option

  datatype 'a node 
    = Stmt of C0.simp * pos * 'a
    | Declare of C0.ty * C0.id * 'a
    | PushScope of 'a
    | PopScope of 'a * int
    | Test of C0.e * pos * 'a * 'a 
    | Return of C0.e option * pos
    | Assert of C0.e * C0.e * C0.pos * 'a
    (* Call is a special node that pushes a scope, declares a variable,
     * and then assigns the result of the function call to it. 
     * It is introduced by the flattening transformation and is not
     * present in the graphs returned from the compiler. *)
    | Call of C0.id * C0.e * C0.e list * C0.pos * 'a 

  fun map f node = 
    case node of
      Stmt (stmt, pc, next) => Stmt (stmt, pc, f next)
    | Declare (ty, x, next) => Declare (ty, x, f next)
    | PushScope next => PushScope (f next)
    | PopScope (next, n) => PopScope (f next, n)
    | Test (test, pc, nextT, nextF) => Test (test, pc, f nextT, f nextF)
    | Return (exp, pc) => Return (exp, pc)
    | Assert (e1, e2, pc, next) => Assert (e1, e2, pc, f next)
    | Call (x, e, es, pc, next) => Call (x, e, es, pc, f next)

  type graph = 
       {entry_point  : pc, 
        nodes        : pc node vector}

  datatype function 
    = Int of {return_type  : C0.ty,
              args         : C0.args,
              graph        : graph}

    | Ext of {return_type : C0.ty,
              args : C0.ty list,
              library : string}

  val fake_pos : Mark.ext = ((0, 0), (0, 0), "__system__")
  val launcher : (pc -> pc node) * pc node = 
      ((fn _ => Return (SOME (C0.Var ("final_result", NONE)), SOME fake_pos)),
       Call (("final_result", NONE), C0.Var ("main", NONE), [], fake_pos, 0))

  val return_ty : function -> C0.ty =
   fn Int {return_type, ...} => return_type
    | Ext {return_type, ...} => return_type

  val arg_tys : function -> C0.ty list = 
   fn Int {args, ...} => List.map #1 args
    | Ext {args, ...} => args

  val args : function -> C0.args =
   fn Int {args, ...} => args
    | Ext {args, ...} =>
      raise Error.Internal "no arg names for internal function"

  val internal_function : function -> bool = fn Int _ => true | Ext _ => false

  val entry_point : function -> pc node = 
   fn Int {graph = {entry_point, nodes}, ...} => Vector.sub (nodes, entry_point)
    | Ext _ => raise Error.Internal "no entry point for internal function"

  val graph : function -> pc -> pc node = 
   fn Int {graph = {nodes, ...}, ...} => (fn pc => Vector.sub (nodes, pc))
    | Ext _ => raise Error.Internal "no graph for internal function"

  val library : function -> string = 
   fn Ext {library, ...} => library
    | Int _ => raise Error.Internal "no library for external function"

  structure MapS = 
  SplayMapFn(struct type ord_key = string val compare = String.compare end)

  type prog = 
      {functions   : function MapS.map, (* C0.fun_name *)
       ty_vars     : C0.ty MapS.map,
       struct_defs : C0.st_fields MapS.map}

  val list_functions : prog -> C0.fun_name list = 
   fn prog => MapS.listKeys (#functions prog)

  val fun_defs : prog -> (C0.fun_name * C0.ty * C0.ty list) list =
   fn {functions, ...} => 
      List.map 
          (fn (f, Int {return_type, args, ...}) =>
              (f, return_type, List.map #1 args)
            | (f, Ext {return_type, args, ...}) => (f, return_type, args))
          (MapS.listItemsi functions)

  val functions : prog -> C0.fun_name -> function option = 
   fn prog => fn f => MapS.find (#functions prog, f)
              
  val ty_vars : prog -> C0.ty_name -> C0.ty option = 
   fn prog => fn t => MapS.find (#ty_vars prog, t)

  val struct_defs : prog -> C0.st_name -> (C0.ty * C0.field_name) list option =
   fn prog => fn s => MapS.find (#struct_defs prog, s)

end

