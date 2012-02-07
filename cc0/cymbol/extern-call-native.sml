(* Facilities for calling dynamically-loaded functions *)
structure NativeCall :> NATIVECALL
                            where type function = NativeFn.t
                              and type native_pointer = MLton.Pointer.t =
struct

  type args = MLton.Pointer.t
  type native_pointer = MLton.Pointer.t
  type function = NativeFn.t

  (* Create passes in the size of the returned value *)
  val create   = _import "args_create":   int -> args;
  val destroy  = _import "args_destroy":  args -> unit;

  (* Add successive arguments *)
  val add_bool = _import "args_add_bool": args * bool * int -> unit;
  val add_int  = _import "args_add_int":  args * Word32.word * int -> unit;
  val add_char = _import "args_add_char": args * char * int -> unit;
  val add_ptr  = _import "args_add_ptr":  args * MLton.Pointer.t * int -> unit;

  (* Call the functon that is represented by a pointer *)
  val apply   = _import "apply":     MLton.Pointer.t * args -> MLton.Pointer.t;

  (* Cast a void* in the intended fashion *)
  val to_bool = _import "cast_bool": MLton.Pointer.t -> bool;
  val to_int  = _import "cast_int":  MLton.Pointer.t -> Word32.word;
  val to_char = _import "cast_char": MLton.Pointer.t -> char;
  val to_ptr  = fn x => x
  val to_void = fn x => ()

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

  fun call (caster: MLton.Pointer.t -> 'a) (fptr, args: arg list): 'a = 
     case fptr of 
        NativeFn.FnPtr t => 
        let val arr = mkargs args
        in caster (apply (t, arr)) before destroy arr
        end
      | NativeFn.Native f =>  
        let val arr = mkargs args
        in caster (f arr) before destroy arr 
        end        

  val call_bool   = call to_bool
  val call_int    = call to_int
  val call_char   = call to_char
  val call_ptr    = call to_ptr
  val call_string =
     ConcreteNativeHeap.rep_to_str 
     o ConcreteNativeHeap.native_to_str 
     o call to_ptr
  val call_void   = call to_void

end
