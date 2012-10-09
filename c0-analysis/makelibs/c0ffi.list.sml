structure Set = 
SplaySetFn (struct type ord_key = string val compare = String.compare end)

structure Map = 
SplayMapFn (struct type ord_key = string val compare = String.compare end)

structure C0ffiList:> sig
   (* read (ROOTDIR: string): Set.set Map.map
    * 
    * Collect lines from ROOTDIR/lib/c0ffi.list into a single datastructure    
    * that maps the name of every known C0 library to the set of functions that
    * are implemented by that library. *)
   val read: string -> Set.set Map.map

   (* write (ROOTDIR: string) (c0ffi_libs: Set.set Map.map): unit 
    * 
    * Given ROOTDIR and the kind of datastructure produced from c0ffi.list by
    * the read function, this function outputs the following: 
      * ROOTDIR/lib/c0ffi.list (write_c0ffi_list)
      * ROOTDIR/vm/c0vm_c0ffi.h (write_c0vm_c0ffi_h)
      * ROOTDIR/vm/c0vm_c0ffi.c (write_c0vm_c0ffi_c)
      * ROOTDIR/compiler/c0vm/c0vm-c0vffi.sml (write_c0vm_c0ffi_sml) *)
   val write: string -> Set.set Map.map -> unit
end = 
struct

(* Given ROOTDIR, returns ROOTDIR/lib/c0ffi.list *)
fun get_filename rootdir = 
   let
      val dirname = OS.Path.joinDirFile {dir = rootdir, file = "lib"}
      val filename = OS.Path.joinDirFile {dir = dirname, file = "c0ffi.list"}
   in 
      filename
   end

(* Some local state used hackishly to make generated code a bit prettier *)
local
(* Given a map from libraries to functions, what's the longest function? *)
val maxLen = 
   Map.foldr 
      (fn (set, max) =>
          Set.foldr (fn (s, max) => Int.max (size s, max)) max set)
      0
val buf = ref 0 (* setBuf sets this to the length of the longest filename *)
val cnt = ref 0 (* setBuf sets this to the total number of library functions *)
in
fun setBuf c0ffi_list =
 ( buf := maxLen c0ffi_list
 ; cnt := Map.foldr (fn (set, count) => count + Set.numItems set) 0 c0ffi_list)
fun getBuf s = 
   CharVector.tabulate (!buf - size s, fn _ => #" ")
fun getCount () = !cnt
end

(* writes lib/c0ffi.list *)
fun write_c0ffi_list rootdir c0ffi_list = 
   let 
      val file = TextIO.openOut (get_filename rootdir)
      val output = fn s => TextIO.output (file, s^"\n")
   in
    ( output "# Automatically generated by bin/wrappergen"
    ; output "# Do not edit this file directly!"
    ; Map.appi 
         (fn (lib, funcs) => 
           ( output ""
           ; output ("lib "^lib)
           ; Set.app output funcs))
         c0ffi_list
    ; TextIO.closeOut file)
   end

(* writes vm/c0vm_c0ffi.h *)
fun write_c0vm_c0ffi_h rootdir c0ffi_list = 
   let 
      val dirname = OS.Path.joinDirFile {dir = rootdir, file = "vm"}
      val hfile = OS.Path.joinDirFile {dir = dirname, file = "c0vm_c0ffi.h"}
      val h = TextIO.openOut hfile
      val output = fn s => TextIO.output (h, s^"\n")
      val gen = let val x = ref 0 in fn () => !x before x := !x + 1 end 
      val toUpper = String.map Char.toUpper
   in
    ( output "/* Automatically generated by bin/wrappergen"
    ; output " * Do not edit this file directly! */"
    ; output "#include \"c0vm.h\""
    ; output ""
    ; output "#ifndef _C0VM_NATIVES_H"
    ; output "#define _C0VM_NATIVES_H"
    ; output ""
    ; output "/* native_fn: the type of generic native functions taking"
    ; output " *            a variable-length array of generic arguments */"
    ; output "typedef c0_value (*native_fn)(c0_value *);"
    ; output ""
    ; output ("#define NATIVE_FUNCTION_COUNT "^Int.toString (getCount ()))
    ; output "extern native_fn native_function_table[NATIVE_FUNCTION_COUNT];"
    ; Map.appi 
         (fn (lib, funcs) => 
           ( output ""
           ; output ("/* "^lib^" */")
           ; Set.app (fn s => 
                       ( output ("#define   NATIVE_"^toUpper s^"              "
                                 ^getBuf s ^Int.toString (gen ()))
                       ; output ("c0_value __c0ffi_"^s^"(c0_value *);")))
                funcs))
         c0ffi_list
    ; output ""
    ; output "#endif /* _C0VM_NATIVES_H */"
    ; TextIO.closeOut h)
   end

(* writes vm/c0vm_c0ffi.c *)
fun write_c0vm_c0ffi_c rootdir c0ffi_list = 
   let 
      val dirname = OS.Path.joinDirFile {dir = rootdir, file = "vm"}
      val cfile = OS.Path.joinDirFile {dir = dirname, file = "c0vm_c0ffi.c"}
      val c = TextIO.openOut cfile
      val output = fn s => TextIO.output (c, s^"\n")
      val toUpper = String.map Char.toUpper
   in
    ( output "/* Automatically generated by bin/wrappergen"
    ; output " * Do not edit this file directly! */"
    ; output "#include \"c0vm_c0ffi.h\""
    ; output ""
    ; output "/* The native function table */"
    ; output "native_fn native_function_table[NATIVE_FUNCTION_COUNT] ="
    ; output "    {"
    ; Map.appi 
         (fn (lib, funcs) => 
           ( output ("      /* "^lib^" */")
           ; Set.app (fn s => 
                       ( output ("      __c0ffi_"^s^",")))
                funcs))
         c0ffi_list
    ; output "    };"
    ; TextIO.closeOut c)
   end

(* writes compiler/c0vm/c0vm-c0ffi.sml *)
fun write_c0vm_c0ffi_sml rootdir c0ffi_list = 
   let 
      val dirname = OS.Path.joinDirFile {dir = rootdir, file = "compiler"}
      val dirname = OS.Path.joinDirFile {dir = dirname, file = "c0vm"}
      val filename = OS.Path.joinDirFile {dir = dirname,file = "c0vm-c0ffi.sml"}
      val file = TextIO.openOut filename
      val output = fn s => TextIO.output (file, s^"\n")
      val gen = let val x = ref 0 in fn () => !x before x := !x + 1 end 
   in
    ( output "(* Automatically generated by bin/wrappergen"
    ; output " * Do not edit this file directly! *)"
    ; output ""
    ; output "signature C0VM_NATIVE = "
    ; output "sig"
    ; output "   val native_index : string -> int"
    ; output "end"
    ; output ""
    ; output "structure C0VMNative :> C0VM_NATIVE = "
    ; output "struct"
    ; output ""
    ; output ("fun native_index(\"\") = "^getBuf ""^"~1")
    ; Map.appi 
         (fn (lib, funcs) => 
           ( output ""
           ; output ("(* "^lib^" *)")
           ; Set.app (fn s => output ("  | native_index(\""^s^"\") = "
                                      ^getBuf s^Int.toString (gen ())))
                funcs))
         c0ffi_list
    ; output ""
    ; output "(* unknown *)"
    ; output ("  | native_index(s) =  "^getBuf ""^"~1")
    ; output ""
    ; output "end"
    ; TextIO.closeOut file)
   end

(* writes cymbol/extern-lib-static.sml *)
fun write_cymbol_extern_lib_static_sml rootdir c0ffi_list = 
   let
      val dirname = OS.Path.joinDirFile {dir = rootdir, file = "cymbol"}
      val filename = OS.Path.joinDirFile 
                       {dir = dirname, file = "extern-lib-static.sml"}
      val file = TextIO.openOut filename
      val output = fn s => TextIO.output (file, s^"\n")
   in
    ( output "(* Automatically generated by bin/wrappergen"
    ; output " * Do not edit this file directly! *)"
    ; output ""
    ; output "structure NativeLibrary :> NATIVELIBRARY where type function\
             \ = NativeFn.t ="
    ; output "struct"
    ; output ""
    ; output "structure Map = "
    ; output "SplayMapFn (struct type ord_key = string \
                           \ val compare = String.compare end)"
    ; output ""
    ; output "type fnptr = MLton.Pointer.t -> MLton.Pointer.t"
    ; output "type function = NativeFn.t"
    ; output "type library = function Map.map"
    ; output ""
    ; output "val mapN = List.map (fn (x, y) => (x, NativeFn.Native y))"
    ; Map.appi
         (fn (lib, funcs) => 
           ( output ""
           ; output ("(* Library "^lib^" *)")
           ; output ("val lib_"^lib^
                     " = List.foldr Map.insert' Map.empty (mapN (")
           ; Set.app 
                (fn s => 
                  ( output ("(\""^s^"\","^getBuf s^"_import \"__c0ffi_"^s^
                            "\" public: fnptr;) ::")))
                funcs
           ; output "[]))"))
         c0ffi_list
    ; output ""
    ; output "fun load _ \"\" = NONE"
    ; Map.appi
         (fn (lib, _) => 
             output ("  | load _ \""^lib^"\" = SOME (lib_"^lib^")"))
         c0ffi_list
    ; output "  | load _ _ = NONE"
    ; output ""
    ; output "fun close _ = ()"
    ; output ""
    ; output "fun get lib sym = Map.find (lib, sym)"
    ; output ""
    ; output "end"
    ; TextIO.closeOut file)
   end

fun write rootdir c0ffi_list = 
 ( setBuf c0ffi_list
 ; write_c0ffi_list rootdir c0ffi_list
 ; write_cymbol_extern_lib_static_sml rootdir c0ffi_list
 ; write_c0vm_c0ffi_sml rootdir c0ffi_list
 ; write_c0vm_c0ffi_h rootdir c0ffi_list
 ; write_c0vm_c0ffi_c rootdir c0ffi_list)

fun read rootdir = 
   let
      val filename = get_filename rootdir
      fun tokenize NONE = NONE
        | tokenize (SOME s) = 
             case String.fields (fn c => c = #"#") s of
                [] => SOME []
              | (s :: _) => SOME (String.tokens Char.isSpace s)

      fun merge_accum NONE libs_accum = libs_accum
        | merge_accum (SOME (lib, funcs)) libs_accum =
             Map.insert (libs_accum, lib, funcs)
 
      (* Collect lines from lib/c0ffi.list into a single datastructure, a
       * Set.set Map.map, which maps the name of each filename to the set
       * of functions that are implemented by that library.
         * file: TextIO.instream - the unread portion of the file
         * lib_accum: string * Set.set - (current library, functions seen)
         * libs_accum: Set.set Map.map - already seen libraries *)
      fun loop file lib_accum libs_accum = 
         case tokenize (TextIO.inputLine file) of
            NONE => merge_accum lib_accum libs_accum before TextIO.closeIn file
          | SOME [] => loop file lib_accum libs_accum
	  | SOME [ "lib" , lib ] =>
               loop file (SOME (lib, Set.empty))
                  (merge_accum lib_accum libs_accum)
	  | SOME [ name ] => 
              (case lib_accum of 
                  NONE => 
                   ( print ("ERROR: function spec `"^name^"' appeared\
                            \ before any library spec `lib foo'\n")
                   ; raise Fail "Bad lib/c0ffi.list")
                | SOME (lib, funcs) => 
                     loop file (SOME (lib, Set.add (funcs, name)))
                        libs_accum)
          | SOME line => 
             ( print ("ERROR: Bad line `"^String.concatWith " " line^"'\n")
             ; raise Fail "Bad lib/c0ffi.list")
   in
      if OS.FileSys.access (filename, [ OS.FileSys.A_READ ]) 
      then loop (TextIO.openIn filename) NONE Map.empty
      else (print ("WARNING: NO FILE `"^filename^"'\n"); Map.empty)
   end

end
