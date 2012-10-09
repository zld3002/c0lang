(* Running with the Cymbol...   *)
(* Robert J. Simmons            *)

signature DEBUGGER = sig

  type state
  type value
  type pc = string * C0.pc
  exception CymbolError of string

  (* Parses a file and loads it into memory *)
  val load : string -> unit

  (* Sets and unsets breakpoint - not implemented *)
  val set_breakpoint : pc -> unit
  val unset_breakpoint : pc -> unit
  val continue : state * pc     -> pc option * state (* Next breakpoint      *)

  (* Debugging functions *)
  val init     : unit           -> state * pc        (* Calls main(), stops  *)
  val step     : state * pc     -> state * pc option (* Takes a single step  *)
  val eval     : state * C0.exp -> state * value     (* Evaluates expression *)

  (* Outputs the whole state *)
  val print_state : state -> unit

  (* Projects out of the opaque value type *)
  exception TypeCast
  val int : value -> int
  val bool : value -> bool
  val string : value -> string
end

structure Debugger :> DEBUGGER = struct

  type pc = string * C0.pc
  fun set_breakpoint _ = raise Match
  fun unset_breakpoint _ = raise Match
  fun continue _ = raise Match

  local
  structure C = Cymbol(Concrete)
  in 
  open C 
  type state = (addr option * pc) C.state
  val int = Word32.toInt o C.int
  end

  fun lib_print (args : value vector) = 
    let val str = string (Vector.sub(args, 0)) 
    in print str; Nothing end

  val program : (string vector * CFG.graph) MapS.map ref = ref MapS.empty

  fun load filename = 
    let
      val file = Parser.parse filename
      fun folder ((name, args, code), prog) = 
        let val cfg = CFG.construct_graph code
        in MapS.insert(prog, name, (args, cfg)) end
    in program := List.foldr folder MapS.empty file end

  (*
  fun call (state, ("print", argv)) = (state, lib_print argv)
    | call (state, (f, argv)) = 
    let 
      val (argn, {entry_point,...}) = MapS.lookup(!program, f)
      val (state, v) = go (push_fun (state, argn, argv), (f, entry_point))
    in (pop_fun state, v) end 
  *)

  (* XXX update state with correct depth *)
  fun fix_depth (state, depth) = state

  fun step_internal (state, (f,pc)) : state * pc option = 
    let 
      (* PERF optimize common case: same function, same graph *)
      val (_,{nodes,...}) = MapS.lookup (!program, f)
      val (node, depth) = Vector.sub (nodes, pc)
      val state = fix_depth (state, depth)
    in
      case node of
        CFG.Command {cmd, next} =>
        let 
          val (state, _) = to_value (state, cmd)
        in 
          (state, SOME (f, next))
        end
      | CFG.Test {test, nextT, nextF} => 
        let 
          val (state, v) = to_value (state, test)
        in
          if bool v 
          then (state, SOME (f,nextT)) 
          else (state, SOME (f,nextF))
        end
      | CFG.FunctionCall {func, args, assign = x, next} => 
        let
          (* Evaluate optional assignment *)
          (* XXX is this the right time to evaluate the assignment part? *)
          val (state : state, answer : addr option) = case x of 
                         NONE => (state, NONE)
                       | SOME x => 
                         let val (state, addr) = to_lvalue (state, x)
                         in (state, SOME addr) end

          (* Evaluate function part to value *)
          (* XXX Function Pointers *)
          val g : string = 
              case func of C0.Var (C0.Normal f) => f | _ => raise Fail "Unimp"

          (* Evaluate arguments to value *)
          fun folder (exp, (state, argv)) = 
            let val (state, v) = to_value (state, exp) 
            in (state, v :: argv) end
          val (state, argv_reversed) = Vector.foldl folder (state,[]) args
          val argv = Vector.fromList(rev argv_reversed)

          (* Lookup function, push call frame and find entry point *)
          val (argn, {entry_point,...}) = MapS.lookup(!program, f)
          val state = push_fun (state, (answer, (f, next)), argn, argv)
        in (state, SOME (g, entry_point)) end
      | CFG.Return {exp} => 
        let
          val (state, v) = to_value (state, exp)
        in
          case pop_fun state of
            NONE => (state, NONE)
          | SOME (state, (NONE, pc)) => (state, SOME pc)
          | SOME (state, (SOME addr, pc)) => (put (state, addr, v), SOME pc)
        end

    end

  (* Initalizes a new state *)
  fun init () = 
    let 
      val (_,{pc_to_extern,entry_point,...}) = (MapS.lookup (!program, "main"))
      val extern_entry_point = case MapI.find (pc_to_extern, entry_point) of
                                 NONE => raise Fail "No extern entry point"
                               | SOME extern_pc => extern_pc
    in (new_state, ("main", extern_entry_point)) end

  (* Takes internal steps until an external step is completed *)
  fun step (state, (f, extern_pc)) = 
    let 
      fun loop (state, NONE) = (state, NONE)
        | loop (state, SOME (g, pc)) = 
          let 
            val () = 
             print ("Function " ^ g ^ " internal PC " ^ Int.toString pc ^ "\n")
            val (_,{pc_to_extern, ...}) = (MapS.lookup (!program, g))
          in
            case MapI.find(pc_to_extern, pc) of 
              NONE => loop (step_internal (state, (g, pc)))
            | SOME extern_pc => (state, SOME(g, extern_pc))
          end
      val (_,{extern_to_pc, ...}) = (MapS.lookup (!program, f))
    in 
      loop (step_internal (state, (f, MapI.lookup (extern_to_pc, extern_pc))))
    end

  (* Evaluates an expression to a value *)
  fun eval (state, exp) = to_value (state, exp)

end
