structure Builtins:> sig
   type impl = (Symbol.symbol * Mark.ext) ConcreteState.state 
               * ConcreteState.value list 
                 -> ConcreteState.value
   datatype builtin =
      Precon of ConcreteState.value list -> unit
    | Impl of impl
   
   val lookup: Symbol.symbol -> builtin
   val reset: {argv: string list} -> unit

   (* Returns true if a library has been completely replaced by builtins *)
   val replaced: string -> bool
end =
struct

structure State = ConcreteState

type impl = (Symbol.symbol * Mark.ext) ConcreteState.state 
            * ConcreteState.value list 
              -> ConcreteState.value
datatype builtin =
   Precon of State.value list -> unit
 | Impl of impl

structure ArgsLib =
struct
   val name = Symbol.symbol "args"
   datatype args_type = ARGS_BOOL | ARGS_INT | ARGS_STRING
   val argv: string list ref = ref []
   val args_list: (args_type * string * State.addr) list ref = ref []
   
   fun args_add (args_type, name, addr) =
    ( args_list := (args_type, State.to_string name, addr) :: !args_list
    ; State.unit)

   fun args_flag (_, name, ptr) =
      case State.to_pointer ptr of 
         NONE => raise Error.AssertionFailed "ptr != NULL [args_flag]"
       | SOME (Ast.Bool, addr) => args_add (ARGS_BOOL, name, addr)
       | _ => raise Error.Dynamic "[args_flag]" 

   fun args_int (_, name, ptr) =
      case State.to_pointer ptr of 
         NONE => raise Error.AssertionFailed "ptr != NULL [args_int]"
       | SOME (Ast.Int, addr) => args_add (ARGS_INT, name, addr)
       | _ => raise Error.Dynamic "[args_int]" 

   fun args_string (_, name, ptr) =
      case State.to_pointer ptr of 
         NONE => raise Error.AssertionFailed "ptr != NULL [args_string]"
       | SOME (Ast.String, addr) => args_add (ARGS_STRING, name, addr)
       | _ => raise Error.Dynamic "[args_string]" 

   fun args_parse state =
   let
      fun lookup x [] = NONE
        | lookup x ((args_type, name, addr) :: l) = 
             if x = name then SOME (args_type, addr)
             else lookup x l

      exception NULL

      val wfromstr = valOf o Word32Signed.fromString
      fun get_int x = 
       ( if size x = 0 then raise NULL else ()
       ; if String.sub (x, 0) = #"-" 
         then Word32.-(Word32Signed.ZERO, 
                       wfromstr (String.extract (x, 1, NONE)))
         else wfromstr x)

      fun loop [] accum = rev accum
        | loop (x :: xs) accum = 
             case lookup x (!args_list) of
                NONE => loop xs (x :: accum)
              | SOME (ARGS_BOOL, ptr) =>
                 ( State.put_addr (state, (Ast.Bool, ptr), State.bool true)
                 ; loop xs accum)
              | SOME (ARGS_INT, ptr) => 
                let val i = State.int (get_int (hd xs))
                in 
                 ( State.put_addr (state, (Ast.Int, ptr), i)
                 ; loop (tl xs) accum)
                end
              | SOME (ARGS_STRING, ptr) => 
                let val s = State.string (hd xs)
                in 
                 ( State.put_addr (state, (Ast.String, ptr), s)
                 ; loop (tl xs) accum)
                end
 
      val args = loop (!argv) []
   in 
      State.null
   end handle _ => State.null

end

fun impl0 f = 
   Impl (fn (state, []) => f state
          | _ => raise Error.Dynamic "Wrong number of arguments [impl1]")

fun impl1 f = 
   Impl (fn (state, [x]) => f (state, x)
          | _ => raise Error.Dynamic "Wrong number of arguments [impl1]")

fun impl2 f = 
   Impl (fn (state, [x,y]) => f (state, x, y)
          | _ => raise Error.Dynamic "Wrong number of arguments [impl2]")

val table = Symbol.digest
   [(Symbol.symbol "args_flag", impl2 ArgsLib.args_flag),
    (Symbol.symbol "args_int", impl2 ArgsLib.args_int),
    (Symbol.symbol "args_string", impl2 ArgsLib.args_string),
    (Symbol.symbol "args_parse", impl0 ArgsLib.args_parse)]

fun reset {argv} = (ArgsLib.argv := argv; ArgsLib.args_list := [])

fun lookup x = 
   case Symbol.look table x of
      NONE => Precon (fn _ => ())
    | SOME f => f

fun replaced x = "args" = x

end
