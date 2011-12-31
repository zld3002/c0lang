structure NativeCall :> NATIVECALL 
   where type function = NativeLibrary.function 
     and type native_pointer = ConcreteState.native_pointer = 
struct 

type function = NativeLibrary.function
type native_pointer = ConcreteState.native_pointer

datatype arg =
   Bool   of bool
 | Int    of Word32.word
 | Char   of char
 | Ptr    of native_pointer
 | String of string

fun call_bool _   = raise Match
fun call_int _    = raise Match
fun call_char _   = raise Match
fun call_ptr _    = raise Match
fun call_string _ = raise Match
fun call_void _   = raise Match

end
