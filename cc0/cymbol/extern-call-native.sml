(* Facilities for calling dynamically-loaded functions *)
structure NativeCall :> NATIVECALL
                            where type function = MLton.Pointer.t
                              and type native_pointer = MLton.Pointer.t =
struct

  type args = MLton.Pointer.t
  type fptr = MLton.Pointer.t
  type native_pointer = MLton.Pointer.t
  type function = fptr

  (* Create passes in the size of the returned value *)
  val create   = _import "args_create":   int -> args;
  val destroy  = _import "args_destroy":  args -> unit;

  (* Add successive arguments *)
  val add_bool = _import "args_add_bool": args * bool * int -> unit;
  val add_int  = _import "args_add_int":  args * Word32.word * int -> unit;
  val add_char = _import "args_add_char": args * char * int -> unit;
  val add_ptr  = _import "args_add_ptr":  args * MLton.Pointer.t * int -> unit;

  (* Call the funciton, get a MLton.Pointer.t to the the turned value *)
  val prim_bool = _import "call_bool":    fptr * args -> bool;
  val prim_int  = _import "call_int":     fptr * args -> Word32.word;
  val prim_char = _import "call_char":    fptr * args -> char;
  val prim_ptr  = _import "call_ptr":     fptr * args -> MLton.Pointer.t;
  val prim_void = _import "call_void":    fptr * args -> unit;

  datatype arg
    = Bool   of bool
    | Int    of Word32.word
    | Char   of char
    | Ptr    of MLton.Pointer.t
    | String of string

  fun mkargs args = 
     let
        val arr = create (List.length args)
        fun loop (n, []) = ()
	  | loop (n, Bool b :: args) = (add_bool (arr, b, n); loop (n+1, args))
	  | loop (n, Int i  :: args) = (add_int  (arr, i, n); loop (n+1, args))
	  | loop (n, Char c :: args) = (add_char (arr, c, n); loop (n+1, args))
	  | loop (n, Ptr p  :: args) = (add_ptr  (arr, p, n); loop (n+1, args))
	  | loop (n, String s :: args) = 
            let 
               val ptr = 
                  ConcreteNativeHeap.str_to_native 
                     (ConcreteNativeHeap.str_to_rep s)
            in
               add_ptr (arr, ptr, n); loop (n+1, args)
	    end
     in
	loop (0, args); arr
     end

  fun call (handler: fptr * args -> 'a) (fptr: fptr, args: arg list): 'a = 
     let
	val arr = mkargs args
	val res = handler (fptr, arr)
     in
	destroy arr; res
     end

  val call_bool   = call prim_bool
  val call_int    = call prim_int
  val call_char   = call prim_char
  val call_ptr    = call prim_ptr
  val call_string =
     ConcreteNativeHeap.rep_to_str 
     o ConcreteNativeHeap.native_to_str 
     o call prim_ptr
  val call_void   = call prim_void

end
