structure CodeTab :> sig
   type fun_ty = Ast.tp * (Ast.tp * Symbol.symbol) list 
   datatype function = 
      Native of fun_ty * NativeCall.function 
    | AbsentNative of fun_ty * string
    | Interpreted of fun_ty * C0Internal.program
   val lookup : Symbol.symbol -> function option
   val list : unit -> Symbol.symbol list
   val reload_libs : string list -> unit
   val reload : Ast.program -> unit
   val print : unit -> unit
end = 
struct

type fun_ty = Ast.tp * (Ast.tp * Symbol.symbol) list 
datatype function = 
   Native of fun_ty * NativeCall.function
 | AbsentNative of fun_ty * string
 | Interpreted of fun_ty * C0Internal.program

structure LibTab = Symtab (type entrytp = NativeLibrary.library)
structure CT = Symtab (type entrytp = function)
open CT

fun vardecl (Ast.VarDecl (x, ty, _, _)) = (ty, x)

fun process_ast pre current_lib = 
 fn Ast.Struct (x, fs, lib, pos) => () (* structs already in Structtab *)

  | Ast.TypeDef (x, tp, pos) => () (* typedefs already in Symtab *)
                                
  | Ast.Function (x, tp, args, NONE, spec, true, pos) => 
    (* This is a library function; make sure we have the impl. *)
    (Flag.guard Flags.flag_verbose
        (fn () => print (pre ^ "Processing " ^ Symbol.name x ^ " (native)\n"))
        ()
     ; case current_lib of 
          NONE => raise Error.Internal ("Library function " ^ Symbol.name x
                                        ^ " outside of any library")
        | SOME (lib_name, NONE) => 
          (Flag.guard Flags.flag_verbose
              (fn () => print (pre ^ "Failed to load; library not present\n"))
              ()
           ; CT.bind (x, AbsentNative ((tp, map vardecl args), lib_name)))
        | SOME (lib_name, SOME lib) => 
          let in
             case NativeLibrary.get lib (Symbol.name x) of
		NONE => 
                (print ("WARNING Function `" ^ Symbol.name x 
			^ "' not present in implementation of library <"
			^ lib_name ^ ">\n")
                 ; CT.bind (x, AbsentNative ((tp, map vardecl args), lib_name)))
	      | SOME impl => 
		CT.bind (x, Native((tp, map vardecl args), impl))
	  end)

  | Ast.Function (x, tp, args, SOME stm, spec, false, SOME pos) => 
    (* This is a defined function; compile it. *)
     ( Flag.guard Flags.flag_verbose
        (fn () => print (pre ^ "Processing " ^ Symbol.name x ^ " (interp)\n"))
        ()
     ; let
          val stms = Isolate.iso_stm (Syn.syn_decls Symbol.empty args) stm
          val func = Compile.cStms (stms @ [Ast.Return NONE]) pos
       in 
          Flag.guards [ Flags.flag_verbose, Flags.flag_print_codes ]
             (fn () => C0Internal.cmdPrint pre func) ()
          ; CT.bind (x, Interpreted ((tp, map vardecl args), func)) 
       end)

  | Ast.Pragma (Ast.UseLib (pragma, SOME prog), pos) =>
    (* This is the code for a library. *)
    (Flag.guard Flags.flag_verbose
        (fn () => print (pre ^ "Loading #use <" ^ pragma ^ ">\n")) ()
     ; app (process_ast (pre ^ " ") 
               (SOME (pragma, LibTab.lookup (Symbol.symbol pragma))))
           prog)

  | Ast.Pragma (Ast.UseFile (pragma, SOME prog), pos) =>
    (* This is the code for a file. *)
    (Flag.guard Flags.flag_verbose
        (fn () => print (pre ^ "Loading #use \"" ^ pragma ^ "\"\n")) ()
     ; app (process_ast (pre ^ " ") NONE) prog)

  | Ast.Function (x, tp, args, NONE, spec, false, pos) => 
    () (* Ignore function prototypes *)

  | Ast.Function (x, tp, args, SOME stm, spec, false, NONE) => 
    raise Error.Internal "Missing position for a defined function"

  | Ast.Function (x, tp, args, SOME stm, spec, true, pos) => 
    raise Error.Internal "A library function cannot be defined!"

  | Ast.Pragma (Ast.Raw (pragma, _), pos) =>
    () (* Ignore random pragmas *)

  | Ast.Pragma (Ast.UseLib (pragma, NONE), pos) =>
    () (* Ignore empty #use <lib> pragmas *)

  | Ast.Pragma (Ast.UseFile (pragma, NONE), pos) =>
    () (* Ignore empty #use "file.c0" pragmas *)

fun load_lib [] lib = print ("WARNING: failed to load library <" ^ lib ^ ">\n")
  | load_lib (libdir :: path) lib =
    let val lib_file = OS.Path.concat(libdir,("lib"^lib^".so")) in
       case NativeLibrary.load libdir lib of
          NONE => 
          (Flag.guard Flags.flag_verbose 
              (fn () => print ("Library " ^ lib_file ^ " did not load\n")) ()
           ; load_lib path lib)
        | SOME lib_ptr =>
          (Flag.guard Flags.flag_verbose
              (fn () => print ("Library " ^ lib_file ^ " loaded\n")) ()
           ; LibTab.bind (Symbol.symbol lib, lib_ptr))
    end

fun reload_libs libs = 
  (app (NativeLibrary.close o valOf o LibTab.lookup) (LibTab.list ())
   ; LibTab.reset ()
   ; app (fn lib => 
             (Flag.guard Flags.flag_verbose
                 (fn () => (print ("Trying to load library " ^ lib ^ "\n"))) ()
              ; load_lib (!Flags.search_path) lib))
         libs)

fun reload prog = (CT.reset (); app (process_ast "" NONE) prog)

fun print_one (x, (tp, args)) = 
   let 
      fun str_args [] = []
        | str_args [(tp, x)] =
             if Flag.isset Flags.flag_dyn_check
                then []
             else [Ast.Print.pp_tp tp^" "^Symbol.name x]
        | str_args ((tp, x) :: args) = 
             (Ast.Print.pp_tp tp^" "^Symbol.name x) :: str_args args
   in
    ( print (Ast.Print.pp_tp tp)
    ; print " "
    ; print (Symbol.name x)
    ; print ("("^String.concatWith ", " (str_args args)^");"))
   end

val print = 
 fn () => app (fn (x, Native (ty, _)) => 
                  (print_one (x, ty); print " // Library function\n")
                | (x, AbsentNative (ty, _)) => 
                  (print_one (x, ty); print " // Broken library function\n")
                | (x, Interpreted (ty, _)) => 
                  (print_one (x, ty); print "\n"))
              (map (fn x => (x, valOf (CT.lookup x))) (CT.list ()))
          
end

