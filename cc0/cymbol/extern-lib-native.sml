structure NativeLibrary :> NATIVELIBRARY where type function = MLton.Pointer.t =
struct
  type library = MLton.Pointer.t
  type function = MLton.Pointer.t

  fun to_mangled_function_name s = "__c0ffi_" ^ s ^ "\000"
  fun tocstr s = s ^ "\000"

  val load_ = _import "lib_open" : string -> library;
  val dlerror = _import "dlerror" : unit -> MLton.Pointer.t;

  fun load lib = 
     let val lib_ptr = load_ (tocstr lib)
     in 
        if lib_ptr = MLton.Pointer.null 
        then 
          (Flag.guard Flags.flag_verbose
              (fn () => 
               let 
                  val offset = ref 0
                  val ptr = dlerror ()
                  val get = fn b => (MLton.Pointer.getWord8 (ptr, !offset)
                                     before 
                                     (if b then offset := !offset +1 else ()))
               in
                  if ptr = MLton.Pointer.null then ()
                  else (print "Library failed to load; dlerror() returned: "
                        ; while get false <> 0wx0 do
                            print (str (Byte.byteToChar (get true))))
                  ; print "\n"
               end) ()
           ; NONE) 
        else SOME lib_ptr 
     end

  val close = _import "dlclose" : library -> unit;

  val get_ = _import "dlsym" : library * string -> function;
  fun get lib sym = 
     let val fptr = get_ (lib, to_mangled_function_name sym) 
     in if MLton.Pointer.null = fptr then NONE else SOME fptr end
end
