structure Set = 
SplaySetFn (struct type ord_key = string val compare = String.compare end)

structure Map = 
SplayMapFn (struct type ord_key = string val compare = String.compare end)

structure C0ffiList = 
struct

fun get_filename rootdir = 
   let
      val dirname = OS.Path.joinDirFile {dir = rootdir, file = "lib"}
      val filename = OS.Path.joinDirFile {dir = dirname, file = "c0ffi.list"}
   in 
      filename
   end

local
val buf = ref 0
val maxLen = 
   Map.foldr 
      (fn (set, max) =>
          Set.foldr (fn (s, max) => Int.max (size s, max)) max set)
      0
val cnt = ref 0
in
fun setBuf c0ffi_list =
 ( buf := maxLen c0ffi_list
 ; cnt := Map.foldr (fn (set, count) => count + Set.numItems set) 0 c0ffi_list)
fun getBuf s = 
   CharVector.tabulate (!buf - size s, fn _ => #" ")
fun getCount () = !cnt
end

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


fun write rootdir c0ffi_list = 
 ( setBuf c0ffi_list
 ; write_c0ffi_list rootdir c0ffi_list
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
