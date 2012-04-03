signature NATIVECALL = sig

  type native_pointer
  type function

  datatype arg 
    = Bool   of bool
    | Int    of Word32.word
    | Char   of char
    | Ptr    of native_pointer
    | String of string

  val call_bool   : function * arg list -> bool
  val call_int    : function * arg list -> Word32.word
  val call_char   : function * arg list -> char
  val call_ptr    : function * arg list -> native_pointer
  val call_string : function * arg list -> string
  val call_void   : function * arg list -> unit
end

signature NATIVELIBRARY =
sig
  type library 
  type function 

  val load : string -> string -> library option
  val close : library -> unit
  val get : library -> string -> function option
end

