structure NativeLibrary :> NATIVELIBRARY where type function = NativeFn.t =
struct
  type library = MLton.Pointer.t
  type function = NativeFn.t

  fun to_mangled_function_name s = "__c0ffi_" ^ s ^ "\000"
  fun tocstr s = s ^ "\000"

  val load_ = _import "lib_open" public: string -> library;
  val dlerror = _import "dlerror" public: unit -> MLton.Pointer.t;

  val lib_ext =
     case List.find (fn (x, y) => x = "sysname") (Posix.ProcEnv.uname ()) of
        SOME (_, "Darwin") => ".dylib"
      | SOME (_, "Linux") => ".so"
      (* XXX these should be some actual exception *)
      | SOME (_, sysname) => 
        raise Error.Internal ("unknown system type, " ^ sysname)
      | _ => 
        raise Error.Internal ("Posix.ProcEnv.uname did not return sysname!")

  fun load libdir lib = 
     let val = lib_file = OS.Path.concat (libdir, "lib" ^ lib ^ lib_ext)
         val lib_ptr = load_ (tocstr lib_file)
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

  val close = _import "dlclose" public: library -> unit;

  val get_ = _import "dlsym" public: library * string -> MLton.Pointer.t;
  fun get lib sym = 
     let val fptr = get_ (lib, to_mangled_function_name sym) 
     in if MLton.Pointer.null = fptr then NONE 
        else SOME (NativeFn.FnPtr fptr) 
     end
end
