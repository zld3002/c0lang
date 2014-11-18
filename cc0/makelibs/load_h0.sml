structure LoadH0 = struct

open Ast

(* Loads a file as if it was passed on the command-line, with no options. *)
fun direct_load file = 
   (Top.reset (); #program (Top.typecheck_and_load [ file ]))

fun error s = 
   (TextIO.output (TextIO.stdErr, "ERROR: " ^ s ^ "\n") 
    ; raise Fail s)

(* This function uses state to output to libs/foo/foo_c0ffi.c *)
val outstream = ref TextIO.stdOut
fun print_endline s = TextIO.output (!outstream, s ^ "\n")

(* This part needs to be knowledgable about the correspondence between C types
 * and C0 types *)
fun string_of_type tp = 
   case tp of 
      Int => "int"
    | Bool => "bool"
    | String => "c0_string"
    | Char => "c0_char"
    | Pointer tp => string_of_type tp ^ " *"
    | Array tp => "c0_array *"
    | StructName id => "struct " ^ Symbol.name id
    | TypeName id => Symbol.name id
    | Void => "void"
    | Any => error "No name for 'any'"
    | FunTypeName _ => error "Cannot cast function types"
    | FunType _ => error "Cannot cast function types"

fun cast_from_type tp = 
   case tp of 
      Int => "(void *) (intptr_t)"
    | Bool => "(void *) (intptr_t)"
    | String => "(void *)"
    | Char => "(void *) (intptr_t)"
    | Pointer tp => "(void *)"
    | Array tp => "(void *)"
    | StructName id => error "Large type in cast (struct)"
    | TypeName id => "(void *)"
    | Void => error "No cast for void"
    | Any => error "No name for 'any'"
    | FunTypeName _ => error "Cannot cast function types"
    | FunType _ => error "Cannot cast function types"

fun cast_into_type tp = 
   case tp of
      Int => "(int) (intptr_t)"
    | Bool => "(bool) (intptr_t)"
    | String => "(c0_string)"
    | Char => "(c0_char) (intptr_t)"
    | Pointer tp => "(" ^ string_of_type tp ^ " *" ^ ")"
    | Array tp => "(c0_array *)"
    | StructName id => error "Large type in cast (struct)"
    | TypeName id => "(" ^ Symbol.name id ^ ")"
    | Void => error "No cast for void"
    | Any => error "No name for 'any'"
    | FunTypeName _ => error "Cannot cast function types"
    | FunType _ => error "Cannot cast function types"

(* Output the header information (if any) associated with a header *)
fun output_header data = 
   case data of 
      Pragma _ => ()
    | Struct (struct_name, NONE, _, _) =>
      print_endline ("struct " ^ Symbol.name struct_name ^ ";")
    | Struct (struct_name, SOME fields, _, _) =>
      let
	 fun print_field (Field (x, tp, _)) = 
	    print_endline ("  " ^ string_of_type tp ^ " " ^ Symbol.name x ^ ";")
      in
	 print_endline ("struct " ^ Symbol.name struct_name ^ "{")
	 ; app print_field fields
         ; print_endline "};"
      end
    | TypeDef (x, tp, _) => 
      print_endline ("typedef " ^ string_of_type tp ^ " " ^ Symbol.name x ^ ";")
    | Function (fun_name, result, params, stm, specs, is_extern, mark) =>
      let
         fun argmap (VarDecl (id, tp, exp, mark)) = 
            if isSome exp then error "VarDecl with expression is impossible"
            else string_of_type tp ^ " " ^ Symbol.name id
 
         val args = 
            String.concatWith ", " (map argmap params)
      in
         print_endline (string_of_type result ^ " " ^ Symbol.name fun_name
                        ^ "(" ^ args ^ ");")
      end
    | FunTypeDef _ => error "Cannot handle function type definitions" 
 
(* Output the function body (if any) associated with a header *)
fun output_wrapper data = 
   case data of 
      Pragma _ => ()
    | Struct _ => ()
    | TypeDef _ => ()
    | Function (fun_name, result, params, stm, specs, is_extern, mark) =>
      let
         (* Build arguments to function call *)
         fun argmap (VarDecl (id, tp, exp, mark)) = 
            if isSome exp then error "VarDecl with expression is impossible"
            else cast_into_type tp

         fun folder (arg, (args: string list, n)) =
            ((argmap arg ^ " args[" ^ Int.toString n ^ "]") :: args, n+1)

         val args = 
            String.concatWith ", " (rev (#1 (foldl folder ([], 0) params)))

         val fun_name = Symbol.name fun_name
      in 
         print_endline ("void *__c0ffi_" ^ fun_name ^ "(void **args) {") 
         ; if null params 
           then print_endline "  (void) args; /* suppress error */" 
           else ()
         ; case result of 
              Void => 
              print_endline ("  " ^ fun_name ^ "(" 
                             ^ args ^ ");\n  return NULL;")
            | result => 
              print_endline ("  return " ^ cast_from_type result ^ " " 
                             ^ fun_name ^ "(" ^ args ^ ");")
         ; print_endline "}"
	 ; print_endline ""
      end
    | FunTypeDef _ => error "Cannot handle function type definitions" 

(* Filter out a header file to get the list of functions *)
fun collect_funs (decl, set) = 
   case decl of 
      Function (fun_name, result, params, stm, specs, is_extern, mark) =>
         Set.add (set, Symbol.name fun_name)
    | _ => set

(* Output the entire file libs/foo/c0ffi_foo.c for the foo library *)
fun load_and_output lib file =
   let 
      val decls = direct_load file
   in
      print_endline ("/* " ^ lib ^ "_c0ffi.c")
      ; print_endline (" * This file automatically generated by the command ")
      ; print_endline (" * 'wrappergen " ^ lib ^ "' - editing is probably bad.")
      ; print_endline (" * ")
      ; print_endline (" * The call to wrappergen was likely probably by ")
      ; print_endline (" * 'make libs/" ^ lib ^ "', which in turn was likely")
      ; print_endline (" * invoked by 'make libs'. */")
      ; print_endline ""
      ; print_endline "#include <inttypes.h>"
      ; print_endline "#include <c0runtime.h>"
      ; print_endline ""
      ; print_endline "/* Headers */"
      ; print_endline ""
      ; app output_header decls
      ; print_endline ""
      ; print_endline "/* Wrappers */"
      ; print_endline ""
      ; app output_wrapper decls
      ; foldl collect_funs Set.empty decls
   end 

(* Main function *)
fun wrappergen (filename, args) =
   let
      val (basedir, lib) = 
         case args of
            [ basedir, lib ] => (basedir, lib)
          | [ lib ] => ("libs", lib)
          | _ => 
            error ("wrong number of arguments.\nUsage: wrappergen [basedir] libname\n")
      val { dir = bindir, ...} = OS.Path.splitDirFile filename
      val () = OS.FileSys.chDir bindir
      val { dir = rootdir, ...} = OS.Path.splitDirFile (OS.FileSys.getDir ())
      val libsdir = OS.Path.joinDirFile {dir = rootdir, file = basedir}
      val libdir = OS.Path.joinDirFile {dir = libsdir, file = lib}
      val h0_file = 
         OS.Path.joinDirFile
            { dir = libdir
            , file = OS.Path.joinBaseExt { base = lib
                                         , ext = SOME "h0"}}
      val c0_file = 
	 OS.Path.joinDirFile
	    { dir = libdir
	    , file = OS.Path.joinBaseExt { base = lib ^ "_c0ffi"
                                         , ext = SOME "c"}}
      val c0ffi_list = C0ffiList.read rootdir
      val () = 
         outstream := TextIO.openOut c0_file
         handle exn =>
          ( TextIO.output (TextIO.stdErr, "FAILED: " ^ exnName exn ^ "\n")
          ; TextIO.output (TextIO.stdErr, exnMessage exn ^ "\n")
          ; OS.Process.exit OS.Process.failure)
      val () = TextIO.output (TextIO.stdErr, "Writing " ^ c0_file ^ "\n")
      val funcs_in_lib = load_and_output lib h0_file
   in
      (* Only do something if the public interface has changed *)
      ( if Map.inDomain (c0ffi_list, lib) 
           andalso Set.equal (funcs_in_lib, Map.lookup (c0ffi_list, lib)) 
        then ()
        else ( print "\n\
                     \***********************************************\n\
                     \* WARNING: THE LIBRARY INTERFACE HAS CHANGED! *\n\
                     \* Do you need to bump the c0vm_version number *\n\
                     \* in c0/compiler/top/top.sml?                 *\n\
                     \***********************************************\n\
                     \\n"
             ; C0ffiList.write rootdir 
                  (Map.insert (c0ffi_list, lib, funcs_in_lib)))
      ; TextIO.closeOut (!outstream)
      ; OS.Process.success)
   end 

end
