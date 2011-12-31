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

  type intern_pc = int
  type extern_pc = int

  datatype 'a node 
    = Decl of C0.ty * C0.variable_name * C0.exp option * 'a
    | Assign of C0.exp * C0.assignop * C0.exp * 'a
    | Call of C0.exp option * C0.exp * C0.exp list * 'a
    | Postop of C0.exp * C0.postop * 'a
    | Noop of 'a
    | PushScope of 'a
    | PopScope of 'a 
    | Test of C0.exp * 'a * 'a 
    | Return of C0.exp option  

  fun map f node = 
    case node of
      Decl (ty, x, exp, next) => Decl (ty, x, exp, f next)
    | Assign (lhs, oper, exp, next) => Assign (lhs, oper, exp, f next)
    | Call (x, lhs, exps, next) => Call (x, lhs, exps, f next)
    | Postop (lhs, oper, next) => Postop (lhs, oper, f next)
    | Noop next => Noop (f next)
    | PushScope next => PushScope (f next)
    | PopScope next => PopScope (f next)
    | Test (test, nextT, nextF) => Test (test, f nextT, f nextF)
    | Return exp => Return exp

  type graph = 
      {entry_point  : intern_pc, 
       nodes        : intern_pc node vector,
       extern_to_pc : intern_pc MapI.map,
       pc_to_extern : extern_pc MapI.map}

  type function = 
      {return_type  : C0.ty,
       args         : (C0.ty * C0.variable_name) list,
       graph        : graph}

  type program = 
      {functions   : function MapS.map,
       ty_vars     : C0.ty MapS.map,
       struct_defs : (C0.ty * string) list MapS.map}

end

