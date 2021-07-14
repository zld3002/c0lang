structure C0ReadLine :> sig 
    val init : unit -> unit 
    val finish : unit -> unit 

    (* Should have the same semantics as TextIO.inputLine TextIO.stdIn
     * i.e. the trailing newline is kept *)
    val readline : string -> string list -> string option
end = struct 

    (* Based off of
     * https://github.com/standardml/readline/blob/master/readline.sml *)
    structure CString =
    struct
        type cstring = string
        type t = MLton.Pointer.t

        val sub = MLton.Pointer.getWord8

        fun toVector t =
            let fun size i = if sub(t, i) = 0w0 then i
                            else size(i+1)
            in  if t <> MLton.Pointer.null then
                    SOME(Word8Vector.tabulate(size 0, fn i => sub(t, i)))
                else NONE
            end

        (* FIXME: Perhaps we ought to do some UTF-8 conversion *)
        val toString = (Option.map Byte.bytesToString) o toVector
        fun toStringVal t = Option.getOpt(toString t, "")

        val free = _import "free" : t -> unit;
    end

    (* c0_readline: string array -> string option 
     * The input array strings should be NUL terminated
     * and the whole array should end with NULL *)
    val c0_readline = _import "c0_readline" : string * MLton.Pointer.t array -> MLton.Pointer.t;

    (* I couldn't figure out how to get a char* ptr from a SML string,
     * so we are jumping through the FFI for it. It looks like
     * whoever wrote coin couldn't figure it out either *)
    val prim_make_c0_string =_import "c0_string_fromcstr" public: string -> MLton.Pointer.t;

    (* Initializes the readline library *)
    val init = _import "c0_readline_init" : unit -> unit;
    (* Writes out history, etc. *)
    val finish = _import "c0_readline_finish" : unit -> unit;

    fun readline prompt completions = 
    let
        (* Construct an array of NUL-terminated strings, and place a NULL
         * pointer at the end of it *)
        fun to_cstr_ptr str = prim_make_c0_string (str ^ "\000")
        val ptrs = Array.fromList (List.map to_cstr_ptr completions @ [MLton.Pointer.null])

        val result_ptr = c0_readline (prompt ^ "\000", ptrs)
        val result = CString.toString result_ptr 
        val () = CString.free result_ptr

        fun add_newline s = s ^ "\n"
    in 
        Option.map add_newline result 
    end 
end 