structure Builtins:> sig
   type precon = (Symbol.symbol * Mark.ext) ConcreteState.state 
                 * ConcreteState.value list 
                   -> unit
   type impl = (Symbol.symbol * Mark.ext) ConcreteState.state 
               * ConcreteState.value list 
                 -> ConcreteState.value
   datatype builtin =
      Precon of precon
    | Impl of impl
   
   val lookup: Symbol.symbol -> builtin
   val reset: {argv: string list} -> unit

   (* Returns true if a library has been completely replaced by builtins *)
   val replaced: string -> bool
end =
struct

structure State = ConcreteState

type precon = (Symbol.symbol * Mark.ext) State.state * State.value list 
                -> unit
type impl = (Symbol.symbol * Mark.ext) State.state * State.value list 
              -> State.value
datatype builtin =
   Precon of precon
 | Impl of impl

fun abort s = raise Error.AssertionFailed ("Assertion failed: "^s)
fun signed_leq (x, y) = not (Word32Signed.signed_less (y, x))

structure ArgsLib =
struct
   val sym_args = Symbol.symbol "args"
   val sym_argc = Symbol.symbol "argc"
   val sym_argv = Symbol.symbol "argv"

   datatype args_type = ARGS_BOOL | ARGS_INT | ARGS_STRING
   val argv: string list ref = ref []
   val args_list: (args_type * string * State.addr) list ref = ref []
   
   fun args_add (args_type, name, addr) =
    ( args_list := (args_type, State.to_string name, addr) :: !args_list
    ; State.unit)

   fun args_flag (_, name, ptr) =
      case State.to_pointer ptr of 
         NONE => abort "ptr != NULL [args_flag]"
       | SOME (Ast.Bool, addr) => args_add (ARGS_BOOL, name, addr)
       | _ => raise Error.Dynamic "[args_flag]" 

   fun args_int (_, name, ptr) =
      case State.to_pointer ptr of 
         NONE => abort "ptr != NULL [args_int]"
       | SOME (Ast.Int, addr) => args_add (ARGS_INT, name, addr)
       | _ => raise Error.Dynamic "[args_int]" 

   fun args_string (_, name, ptr) =
      case State.to_pointer ptr of 
         NONE => abort "ptr != NULL [args_string]"
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
 
      val res = State.alloc (state, Ast.StructName sym_args)
      val res_addr = #2 (valOf (State.to_pointer res))
      val res_argc = State.offset_field (state, res_addr, sym_args, sym_argc)
      val res_argv = State.offset_field (state, res_addr, sym_args, sym_argv)

      val val_argc = Word32.fromInt (length args)
      val () = State.put_addr (state, res_argc, State.int val_argc)

      val val_argv = State.alloc_array (state, Ast.String, val_argc)
      val () = State.put_addr (state, res_argv, val_argv)
      val addr_argv = #2 (State.to_array val_argv) 
      fun argloop n [] = ()
        | argloop n (arg :: args) = 
          let val addr = State.offset_index (state, addr_argv, n)
          in 
           ( State.put_addr (state, (Ast.String, addr), State.string arg) 
           ; argloop (n+1) args) 
          end
      val () = argloop 0 args
   in res
   end handle _ => State.null
end

structure FileLib =
struct
   (* We need to know how to inspect the internal state of a file_t *)
   (* This is a bit dangerous; we're extending the library nefariously... *)
   val struct_file_loaded = ref false
   val sym_file = Symbol.symbol "file"
   val sym_handle = Symbol.symbol "handle"
   val sym_isEOF = Symbol.symbol "isEOF"
   val FILEptr = Ast.Pointer (Ast.StructName (Symbol.symbol "FILE_header"))
   fun load_struct_file () =
      if !struct_file_loaded then ()
      else
      let
         val fields = [Ast.Field (sym_handle, FILEptr, NONE),
                       Ast.Field (sym_isEOF, Ast.Bool, NONE)]
         val gdecl = Ast.Struct(sym_file, SOME fields, true, NONE)
      in 
         Structtab.bind (sym_file, gdecl)
      end

   fun file_base_addr (state, f) = 
      case State.to_pointer f of
         NONE => abort "ptr != NULL"
       | SOME (_, addr) => addr

   fun file_closed (state, f) =
   let
      val () = load_struct_file ()
      val addr = file_base_addr (state, f)
      val addr_handle = State.offset_field (state, addr, sym_file, sym_handle)
      val val_handle = State.get_addr (state, addr_handle)
   in
      case State.to_pointer val_handle of 
         NONE => true
       | SOME _ => false 
   end

   fun file_eof (state, f) = 
   let
      val () = load_struct_file ()
      val addr = file_base_addr (state, f)
      val addr_isEOF = State.offset_field (state, addr, sym_file, sym_isEOF)
      val val_isEOF = State.get_addr (state, addr_isEOF)
   in
      State.to_bool val_isEOF
   end

   fun file_close_precon (state, f) =
    ( if isSome (State.to_pointer f) then ()
         else abort "f != NULL [file_close]"
    ; if not (file_closed (state, f)) then ()
         else abort "!file_closed(f) [file_close]")

   fun file_readline_precon (state, f) = 
    ( if isSome (State.to_pointer f) then ()
         else abort "f != NULL [file_readline]"
    ; if not (file_closed (state, f)) then ()
         else abort "!file_closed(f) [file_readline]"
    ; if not (file_eof (state, f)) then ()
         else abort "!file_eof(f) [file_readline]")
end

structure ImageLib = 
struct
   fun image_create (state, width, height) = 
    ( if Word32Signed.signed_less (Word32Signed.ZERO, State.to_int width)
         then () 
         else abort "0 < width [image_create]" 
    ; if Word32Signed.signed_less (Word32Signed.ZERO, State.to_int height) 
         then () 
         else abort "0 < height [image_create]" )
 
   fun image_clone (state, src) =
      if isSome (State.to_pointer src) then ()
         else abort "src != NULL [image_clone]"
 
   fun image_width (state, src) =
      if isSome (State.to_pointer src) then ()
         else abort "src != NULL [image_width]"
 
   fun image_height (state, src) =
      if isSome (State.to_pointer src) then ()
         else abort "src != NULL [image_height]"
 
   fun image_data (state, src) =
      if isSome (State.to_pointer src) then ()
         else abort "src != NULL [image_data]"
 
   fun image_subimage (state, src, x, y, width, height) =
      if isSome (State.to_pointer src) then ()
         else abort "src != NULL [image_data]"

   fun image_save (state, src, path) =
      if isSome (State.to_pointer src) then ()
         else abort "src != NULL [image_data]"
end

structure ParseLib =
struct
   fun parse_int (state, s, base) = 
   let val base = State.to_int base
   in
    ( if signed_leq (Word32.fromInt 2, base) then () 
         else abort "2 <= base [parse_int]" 
    ; if signed_leq (base, Word32.fromInt 36) then () 
         else abort "base <= 36 [parse_int]")
   end
end

structure StringLib =
struct

   fun string_charat (state, s, idx) = 
   let val strlen = Word32.fromInt (size (State.to_string s))
   in
    ( if signed_leq (Word32.fromInt 0, State.to_int idx) then ()
         else abort "0 <= idx [string_charat]"
    ; if Word32Signed.signed_less (State.to_int idx, strlen) then ()
         else abort "idx < string_length(s) [string_charat]")
   end

   fun string_sub (state, s, idx_start, idx_end) = 
   let val strlen = size (State.to_string s)
   in
    ( if signed_leq (Word32.fromInt 0, State.to_int idx_start) then ()
         else abort "0 <= start [string_sub]"
    ; if signed_leq (State.to_int idx_start, State.to_int idx_end) then ()
         else abort "start <= end [string_sub]"
    ; if signed_leq (State.to_int idx_end, Word32.fromInt strlen) then ()
         else abort "end <= string_length(a) [string_sub]")
   end

   fun string_terminated (state, A) = 
   let
      val (ty_char, addr, len) = State.to_array A 
      fun read n = 
         State.to_char 
            (State.get_addr (state, (ty_char, State.offset_index 
                                                 (state, addr, n))))
      fun loop n = 
         if n = len then false
         else if #"\^@" = read n then true 
         else loop (n+1)
   in
      loop 0
   end 

   fun from_chararray (state, A) =
   let val (_, _, len) = State.to_array A
   in
      (* Gotta match the library's behavior and segfault, though
       * that's a bit asinine - rjs 12/29/2012*)
      if string_terminated (state, A) then ()
         else raise Error.ArrayOutOfBounds (len, len)
   end

   fun char_chr (state, n) = 
    ( if signed_leq (Word32.fromInt 0, State.to_int n) then () 
         else abort "0 <= n [char_chr]" 
    ; if signed_leq (State.to_int n, Word32.fromInt 127) then () 
         else abort "n <= 127 [char_chr]")
end

fun impl0 f = 
   Impl (fn (state, []) => f (state)
          | _ => raise Error.Dynamic "Wrong number of arguments [impl1]")

fun impl1 f = 
   Impl (fn (state, [x]) => f (state, x)
          | _ => raise Error.Dynamic "Wrong number of arguments [impl1]")

fun impl2 f = 
   Impl (fn (state, [x,y]) => f (state, x, y)
          | _ => raise Error.Dynamic "Wrong number of arguments [impl2]")

fun precon0 f = 
   Precon (fn (state, []) => f (state)
            | _ => raise Error.Dynamic "Wrong number of arguments [precon0]")

fun precon1 f = 
   Precon (fn (state, [x]) => f (state, x)
            | _ => raise Error.Dynamic "Wrong number of arguments [precon1]")

fun precon2 f = 
   Precon (fn (state, [x, y]) => f (state, x, y)
            | _ => raise Error.Dynamic "Wrong number of arguments [precon2]")

fun precon3 f = 
   Precon (fn (state, [x, y, z]) => f (state, x, y, z)
            | _ => raise Error.Dynamic "Wrong number of arguments [precon3]")

fun precon5 f = 
   Precon (fn (state, [x1, x2, x3, x4, x5]) => f (state, x1, x2, x3, x4, x5)
            | _ => raise Error.Dynamic "Wrong number of arguments [precon5]")

val table = Symbol.digest
   [
    (Symbol.symbol "args_flag", impl2 ArgsLib.args_flag),
    (Symbol.symbol "args_int", impl2 ArgsLib.args_int),
    (Symbol.symbol "args_string", impl2 ArgsLib.args_string),
    (Symbol.symbol "args_parse", impl0 ArgsLib.args_parse),
    
    (Symbol.symbol "file_closed", impl1 (State.bool o FileLib.file_closed)),
    (Symbol.symbol "file_close", precon1 FileLib.file_close_precon),
    (Symbol.symbol "file_eof", impl1 (State.bool o FileLib.file_eof)),
    (Symbol.symbol "file_readline", precon1 FileLib.file_readline_precon),

    (Symbol.symbol "image_create", precon2 ImageLib.image_create),
    (Symbol.symbol "image_clone", precon1 ImageLib.image_clone),
    (Symbol.symbol "image_width", precon1 ImageLib.image_width),
    (Symbol.symbol "image_height", precon1 ImageLib.image_height),
    (Symbol.symbol "image_data", precon1 ImageLib.image_data),
    (Symbol.symbol "image_subimage", precon5 ImageLib.image_subimage),
    (Symbol.symbol "image_save", precon2 ImageLib.image_save),

    (Symbol.symbol "parse_int", precon2 ParseLib.parse_int),

    (Symbol.symbol "string_charat", precon2 StringLib.string_charat),
    (Symbol.symbol "string_sub", precon3 StringLib.string_sub),
    (Symbol.symbol "string_from_chararray", precon1 StringLib.from_chararray),
    (Symbol.symbol "char_chr", precon1 StringLib.char_chr)
    ]

fun reset {argv} = (ArgsLib.argv := argv; ArgsLib.args_list := [])

fun lookup x = 
   case Symbol.look table x of
      NONE => Precon (fn _ => ())
    | SOME f => f

fun replaced x = "args" = x

end
