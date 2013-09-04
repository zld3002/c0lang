(* C0 Compiler
 * Top Level Environment
 * Frank Pfenning <fp@cs.cmu.edu>
 * William Lovas <wjl@cs.cmu.edu>
 * Rob Simmons <rjsimmon@cs.cmu.edu>
 *)

signature TOP =
sig
  (* main function for standalone executable
   * use with SMLofNJ.exportFn("heapfilename", Top.main)
   *)
  val main : string * string list -> OS.Process.status
  
  (* test "arguments"; is the same as executing a saved
   * heap with arguments on the command line
   *)
  val test : string -> OS.Process.status

  (* External hooks *)
  exception EXIT
  val reset : unit -> unit
  val get_sources_set_flags : 
      {options: unit GetOpt.opt_descr list,
       usageinfo: string,
       versioninfo: string,
       errfn: string -> unit,
       args: string list}
      -> string list
  val typecheck_and_load : 
      string list -> {library_headers : Ast.program, program : Ast.program,
                      oprogram : Ast.program, sprogram : Ast.program}
  val finalize : 
      {library_headers : Ast.program} -> {library_wrappers: Ast.program}
  val static_analysis : Ast.program -> unit
end

structure Top :> TOP =
struct
  structure G = GetOpt  (* from $/smlnj-lib/Util/getopt-sig.sml *)

  (* printing error messages *)
  fun say s = TextIO.output (TextIO.stdErr, s ^ "\n")
  fun newline () = TextIO.output (TextIO.stdErr, "\n")

  (* path concatenation, make result canonical *)
  fun path_concat (x, y) = OS.Path.mkCanonical (OS.Path.concat (x, y))
  fun path_concat3 (x, y, z) = 
      OS.Path.mkCanonical (OS.Path.concat (x, OS.Path.concat (y, z)))

  exception EXIT  (* some error, exit with failure, exported *)
  exception FINISHED  (* no error, exit with success, internal only *)

  fun readable file = OS.FileSys.access (file, [OS.FileSys.A_READ])

  val lib_ext =
      (* on Cygiwn, static libs are used (see top/flags.sml *) 
      if Flag.isset Flags.flag_static then 
        ".a"
      else
        case List.find (fn (x, y) => x = "sysname") (Posix.ProcEnv.uname ()) of
            SOME (_, "Darwin") => ".dylib"
          | SOME (_, "Linux") => ".so"
          (*| SOME (_, "CYGWIN_NT-6.1") => ".dll" *)
          (* XXX these should be some actual exception *)
          | SOME (_, sysname) => 
              if String.isPrefix "CYGWIN" sysname then
                ".dll"
              else
                raise Fail ("unknown system type, " ^ sysname)
          | _ => raise Fail ("Posix.ProcEnv.uname did not return sysname!")

  fun native_lib_name name = "lib" ^ name ^ lib_ext

  fun get_library_archive name =
      let
          val candidates =
              map (fn path => path_concat (path, native_lib_name name))
                  (!Flags.search_path)
      in (* improve this error message, now that we have #use <lib>? *)
          case List.find readable candidates of
            NONE => (say ("Could not find " ^ native_lib_name name); raise EXIT)
          | SOME s => s
      end

  fun abspath rpath = OS.Path.mkAbsolute 
                          { path = rpath, relativeTo = OS.FileSys.getDir () }

  fun get_library_header name = 
      let
          val candidates =
              List.foldr (fn (path, cands) => path_concat (path, name ^ ".h0")
                                              :: path_concat (path, name ^ ".h1")
                                              :: cands)
                         nil
                         (!Flags.search_path)
              (* 
              map (fn path => path_concat (path, name ^ ".h0"))
                  (!Flags.search_path)
               *)
      in (* improve this error message, now that we have #use <lib>? *)
          case List.find readable candidates of
            NONE => (say ("Could not find " ^ name ^ ".h0"); raise EXIT)
          | SOME s => s
      end

  fun get_library_source name =
      let
	  val candidates =
	      List.foldr (fn (path, cands) => path_concat (path, name ^ ".c0")
                                              :: path_concat (path, name ^ ".c1")
                                              :: cands)
                         nil
	                 (!Flags.search_path)
      in
	  List.find readable candidates
      end

  fun check_language_standard filename ast =
      let
          val {base=_, ext=file_ext} = OS.Path.splitBaseExt filename
      in
          case file_ext
           of SOME("l1") => StdL1.check ast
            | SOME("c0") => StdC0.check ast
            | SOME("h0") => StdC0.check ast
            | SOME("c1") => () (* nothing to check at the moment *)
            | SOME("h1") => () (* nothing to check at the moment *)
            | _ => (* unknown or missing extension; apply default standard *)
              (case !Flags.standard
                of "l1" => StdL1.check ast
                 | "c0" => StdC0.check ast
                 | "c1" => ()
                 | std => ( say ("Unknown language standard '" ^ std ^ "'")
                          ; raise EXIT ))
      end

  fun lex_annos filename =
      let
          val {base=_, ext=file_ext} = OS.Path.splitBaseExt filename
      in
          case file_ext
           of SOME("l1") => false
            | SOME("c0") => true
            | SOME("h0") => true
            | SOME("c1") => true
            | SOME("h1") => true
            | _ => (* unknown or missing extension; apply default standard *)
              (case !Flags.standard
                of "l1" => false
                 | "c0" => true
                 | "c1" => true
                 | std => ( say ("Unknown language standard '" ^ std ^ "'")
                          ; raise EXIT ))
      end

  fun is_fundef (Ast.Function(_, _, _, SOME(s), _, _, _)) = true
    | is_fundef _ = false

  fun extract_wrappers (Ast.Pragma (Ast.UseLib (library, SOME(gdecls)), _)::libs) =
        List.filter is_fundef gdecls @ extract_wrappers libs
    | extract_wrappers (_::libs) = raise Fail("internal error: library misconfiguration")
    | extract_wrappers nil = nil

  val lib_file = "stdc0.h0"
  val cc0_lib = "cc0lib.h"	(* using .h *)
  val cc0_main = "cc0main.c"	(* using .c *)       

  (* Reset all the internal tables of the compiler and all flags *)
  fun reset () =
      ( ParseState.reset ()	(* reset file name and line info *)
      ; ErrorMsg.reset ()	(* reset error message info *)
      ; Structtab.reset ()	(* reset global struct table *)
      ; Symtab.reset ()		(* reset global symbol table *)
      ; Typetab.reset ()	(* reset type table *)
      ; Funversiontab.reset ()	(* reset function version table *)
      ; Libtab.reset ()	        (* reset library and file loaded table *)
      ; Filetab.reset ()	(* reset file loaded table *)
      ; Symset.reset () )       (* reset set of undefined, but used functions *)

  (* Read command line, get list of sources *)
  fun get_sources_set_flags {options, versioninfo, usageinfo, errfn, args} = 
      let val sources = Flags.reset_flags options errfn args
      in
          ( if Flag.isset Flags.flag_version
            then (say versioninfo ; raise EXIT)
            else ()
	  ; if Flag.isset Flags.flag_help orelse not (isSome sources)
	    then (say versioninfo ; say usageinfo ; raise EXIT)
	    else ()
          ; if Flag.isset Flags.flag_dyn_check andalso !Flags.runtime = "unsafe"
            then ( say "unsafe runtime (-runsafe) cannot be \
                       \combined with dynamic checks (-d)"
                 ; raise EXIT)
            else ()
	  ; valOf sources )
      end

  (* After reset, take a list of sources, typecheck them, and load them *)
  fun typecheck_and_load sources = 
      let
        (* For each library -lfoo find foo.h0, load, and typecheck.  *)
        fun process_library_header' library = 
            let 
		val libsym = Symbol.symbol library
	    in
		case Libtab.lookup libsym
		 of SOME(_) =>
		    ( Flag.guard Flags.flag_verbose
		      (fn () => say ("Skipping library " ^ library ^ " - already loaded")) ()
		    ; NONE )
                  | NONE =>
		    let 
			val library_h0 = get_library_header library
			val library_c0_opt = get_library_source library
			val () = Libtab.bind (libsym, case library_c0_opt of NONE => true | SOME _ => false)
			val () = Flag.guard Flags.flag_verbose
				 (fn () => say ("Reading library header " ^ library_h0 ^ " ...")) ()
                        val () = ( C0Lex.warnings := Flag.isset Flags.flag_warn )
                        val () = ( C0Lex.lexAnnos := lex_annos library_h0 )
			val ast = Parse.parse library_h0 process_library_header process_usefile
			val () = Flag.guard Flags.flag_ast
				 (fn () => say (Ast.Print.pp_program ast)) ()
		    in
			case library_c0_opt
			 of NONE =>
			    let val () = Flag.guard Flags.flag_verbose
					 (fn () => say ("Checking library " ^ library_h0 ^ " ...")) ()
				(* true : is library *)
                                val () = check_language_standard library_h0 ast
				val ast' = TypeChecker.typecheck(ast, true) 
				val () = Flag.guards [Flags.flag_verbose, Flags.flag_dyn_check]
					 (fn () => say ("Transforming contracts on library " ^ library_h0  ^ " ...")) ()
				val ast'' = if Flag.isset Flags.flag_dyn_check
					    then DynCheck.contracts ast'
					    else ast'
			    in 
				SOME ast''
			    end
			  | SOME(library_c0) =>
			    let val () = Flag.guard Flags.flag_verbose
					 (fn () => say ("Reading library implementation " ^ library_c0 ^ " ...")) ()
                                val () = ( C0Lex.warnings := Flag.isset Flags.flag_warn )
                                val () = ( C0Lex.lexAnnos := lex_annos library_c0 )
				val ast' = Parse.parse library_c0 process_library_header process_usefile
				val () = Flag.guard Flags.flag_ast
					 (fn () => say (Ast.Print.pp_program ast)) ()
				(* false : do not treat as library, because functions are not external! *)
				val () = Flag.guard Flags.flag_verbose
					 (fn () => say ("Checking library " ^ library ^ " ...")) ()
                                val () = check_language_standard library_h0 ast
                                val () = check_language_standard library_c0 ast'
				val ast'' = TypeChecker.typecheck(ast @ ast', false)
				val () = Flag.guards [Flags.flag_verbose, Flags.flag_dyn_check]
					 (fn () => say ("Transforming contracts on library " ^ library ^ " ...")) ()
				val ast''' = if Flag.isset Flags.flag_dyn_check
					     then DynCheck.contracts ast''
					     else ast''
			    in
				SOME ast'''
			    end
		    end 
	    end

        and process_program' source_c0 = 
            let 
		val filesym = Symbol.symbol (OS.Path.mkCanonical source_c0)
	    in
		case Filetab.lookup filesym
		 of SOME() =>
		    ( Flag.guard Flags.flag_verbose
		      (fn () => say ("Skipping file " ^ source_c0 ^ " - already loaded")) ()
		    ; NONE )
		  | NONE =>
		    let val () = Filetab.bind (filesym, ())
			val () = Flag.guard Flags.flag_verbose
				 (fn () => say ("Parsing file " ^ source_c0 ^ " ...")) ()
                        val () = ( C0Lex.warnings := Flag.isset Flags.flag_warn )
                        val () = ( C0Lex.lexAnnos := lex_annos source_c0 )
			val ast = Parse.parse source_c0 process_library_header
                                              process_usefile
			val () = Flag.guard Flags.flag_ast
		                 (fn () => say (Ast.Print.pp_program ast)) ()
			val () = Flag.guard Flags.flag_verbose
				 (fn () => say ("Checking file " ^ source_c0 ^ " ...")) ()
                        (* false : is not library *)
                        val () = check_language_standard source_c0 ast
			val ast' = TypeChecker.typecheck(ast, false)
			val () = Flag.guards [Flags.flag_verbose, Flags.flag_dyn_check]
				 (fn () => say ("Transforming contracts on file " ^ source_c0 ^ " ...")) ()
			val ast'' = if Flag.isset Flags.flag_dyn_check
				    then DynCheck.contracts ast'
				    else ast'
		    in
			SOME (ast'', ast', ast)
		    end
	    end

        and process_program source_c0 = 
            case process_program' source_c0 of
               NONE => ([],[],[])
             | SOME (prog'', prog', prog) => (prog'', prog', prog)

        and process_library_header source_c0 = 
            case process_library_header' source_c0 of
               NONE => []
             | SOME prog => prog

        and process_usefile source_c0 use_file =
	    let
		val {dir = src_dir, file = _} = OS.Path.splitDirFile source_c0
		val use_source = OS.Path.concat (src_dir, use_file)
	    in
		#1 (process_program use_source)
	    end

        fun pragmaify_library library = 
            Ast.Pragma 
                (Ast.UseLib (library, process_library_header' library), NONE)

        val library_headers = 
            map pragmaify_library (!Flags.libraries)
        (* At this point, the declarations for all of the included libraries
	 * are in the global symbol table, marked as extern *)

        (* process multiple programs in sequence, left-to-right *)
        val programs = (map process_program sources)
        (* extract the contract-transformed programs and the original programs *)
        val tprogram = List.concat (map #1 programs)
        val oprogram = List.concat (map #2 programs)
        val sprogram = List.concat (map #3 programs)
   in
      (* propagate original source program (sprogram) here? *)
      {library_headers = library_headers, program = tprogram,
       oprogram = oprogram, sprogram = sprogram}
   end

fun finalize {library_headers} = 
    let
        (* check all functions are defined *)
	val () = TypeChecker.check_all_defined () 

        (* at this point all libraries, aux files, and main files
         * have been loaded and processed
         *)
        (* create true list of loaded native libraries, including those from 
         * #use <lib> *)
        (* exclude source libraries here *)
	val () = ( Flags.libraries :=
		   map Symbol.name 
                       (List.filter (fn libsym => valOf (Libtab.lookup libsym))
				    (Libtab.list())))

        (* the wrappers are only for those libraries specified
         * one the command line with -l, #use <lib> are in-lined
         *)
        val library_wrappers = extract_wrappers library_headers
      in 
        { library_wrappers = library_wrappers } 
      end

fun static_analysis oprogram = 
let
        (* Run purity check *)
        val _ = Flag.guard Flags.flag_purity_check 
	           (fn () => 
	             let val verrors = AnalysisTop.purityCheck oprogram
	                 val _ = map (say o VError.pp_error) verrors
	             in 
	                 case verrors of
	                    [] => ()
	                  | _ => raise EXIT (* die on error. *)
	             end) ()
        (* Run static checking *)
        val _ = Flag.guard Flags.flag_static_check 
	           (fn () => 
	             let val verrors = AnalysisTop.staticCheck oprogram
	                 val _ = map (say o VError.pp_error) verrors
	                 val _ = case verrors of
	                            [] => say "No static errors."
	                          | _ => ()
	             in 
                         (* Static check does not compile the program. *)
	                 raise FINISHED
	             end) ()
        (* Run verification condition checking *)
        val _ = Flag.guard Flags.flag_verif_check 
	           (fn () => 
	             let val verrors = AnalysisTop.verifCheck oprogram
	                 val _ = map (say o VError.pp_error) verrors
	                 val _ = case verrors of
	                            [] => say "No verification condition errors could be found."
	                          | _ => ()
	             in 
                         (* Verification conditions check does not compile the program. *)
	                 raise FINISHED
	             end) ()
  in () end	             

  fun main (name, args) =
      let
        val usage = 
            if "sml" = #file (OS.Path.splitDirFile (CommandLine.name ()))
            then ("Top.test \"[OPTION...] SOURCEFILE\";")
            else ("cc0 [OPTION...] SOURCEFILE")
	val header = "Usage: " ^ usage ^ "\nwhere OPTION is"
        val options = Flags.core_options @ Flags.compiler_options
        val versioninfo = "C0 reference compiler (cc0) revision "
                        ^ BuildId.revision ^ " (built " ^ BuildId.date ^ ")"
	val usageinfo = G.usageInfo {header = header, options = options}
	val c0vm_version = 4
	fun errfn msg : unit = (say (msg ^ "\n" ^ usageinfo) ; raise EXIT)

        (* Reset state by reading argments; possibly display usage & exit. *) 
        val () = if List.length args = 0
		 then (say versioninfo; say usageinfo; raise EXIT)
		 else reset ()
        val sources = get_sources_set_flags
                          {options = options,
                           errfn = errfn,
                           versioninfo = versioninfo,
                           usageinfo = usageinfo,
                           args = args}
	val () = if null sources then errfn "Error: no input file" else ()
        val () = (* not (null (!runtime_args)) => Flag.isset Flag.flag_exec *)
                 if null (!Flags.runtime_args)
                    orelse Flag.isset Flags.flag_exec then ()
                 else errfn "Error: -a in cc0 only makes sense combined with -x"

        (* copy sources, record command line *)
        val () =
            if Flag.isset Flags.flag_no_log then ()
            else
                let fun sanitize_char #"'" = #"#"
                      | sanitize_char c = c
                    fun shell_quote s = "'" ^ String.map sanitize_char s ^ "'"
		    val cmd_name = abspath (CommandLine.name ())
                    val {dir, ...} = OS.Path.splitDirFile (cmd_name)
                    val cpfiles_bin = path_concat (dir, "cpfiles")
		    val cmd = (cpfiles_bin
                               ^ " "
                               ^ shell_quote (String.concatWith " "
						(CommandLine.name () ::
						 CommandLine.arguments ()))
                               ^ " "
                               ^ String.concatWith " " (map shell_quote sources))
		    (* val _ = print (cmd ^ "\n") *)
                in
                    if OS.FileSys.access (cpfiles_bin, [OS.FileSys.A_READ,OS.FileSys.A_EXEC])
		    then ignore (OS.Process.system cmd)
                    else ()
                end

        (* Declare main before loading any libraries *)
	val main = Symbol.symbol "main"
	val () = Symtab.bind(main, Ast.Function(main, Ast.Int, nil, NONE, nil, false, NONE))
	val () = Symset.add main; (* main is implicitly used *)

        (* Load the program into memory *)
        val {library_headers, program, oprogram, sprogram} = typecheck_and_load sources
        val {library_wrappers} = finalize {library_headers = library_headers}
        val () = if Flag.isset Flags.flag_warn
                 then Warn.warn_program sprogram
                 else ()

        val () = static_analysis oprogram

        (* Check to make sure we're not trying to output a .c0 or .h0 file. *)
        val {dir = _, file = a_out_file} = OS.Path.splitDirFile (!Flags.a_out)
        val {base = _, ext = a_out_extOpt} = OS.Path.splitBaseExt a_out_file
        val () = case a_out_extOpt of
                    SOME "c0" => ( say ("Cannot produce .c0 files as output.\n"
                                        ^ "This would overwrite " ^ a_out_file 
                                        ^ " if it exists.\n") ;
                                   raise EXIT )
                  | SOME "h0" => ( say ("Cannot produce .h0 files as output.\n"
                                        ^ "This would overwrite " ^ a_out_file 
                                        ^ " if it exists.\n") ;
                                   raise EXIT )
                  | _ => () 

        (* Determine output files Based on the initial files *)
        (* use last input file as name for intermediate .c and .h files *)
	val last_source = List.last sources
        val {dir = out_dir, file = out_file} = OS.Path.splitDirFile last_source
        val {base = out_base, ext = extOpt} = OS.Path.splitBaseExt out_file
	val () = case extOpt
		  of SOME "c" => ( say ("Compilation would overwrite " 
                                        ^ last_source ^ "\n"
					^ "should source be " ^ out_file 
                                        ^ ".c0 ?") ;
				   raise EXIT )
		   | SOME "h" => ( say ("Compilation would overwrite " 
                                        ^ last_source ^ "\n"
					^ "do not compile .h files") ;
				   raise EXIT )
		   | _ => () 
        val cname = OS.Path.joinBaseExt {base = out_base, ext = SOME "c0.c"}
        val hname = OS.Path.joinBaseExt {base = out_base, ext = SOME "c0.h"}
	val bcfile = if !Flags.a_out = "a.out" (* if no output specified with -o *)
		    then path_concat (out_dir, OS.Path.joinBaseExt {base = out_base, ext = SOME "bc0"})
		    else !Flags.a_out (* if specified with -o *)
        val () = if Flag.isset Flags.flag_bytecode
		then let val () = Flag.guard Flags.flag_verbose
				  (fn () => say ("Writing bytecode file to " ^ bcfile ^ " ...")) ()
			 val all_program = library_wrappers @ program
			 val bytecode = C0VMTrans.trans (!Flags.bytecode_arch) all_program
			 val bcstring = C0VMPrint.pp_program c0vm_version (!Flags.bytecode_arch) bytecode
			 val () = SafeIO.withOpenOut bcfile
				  (fn bstream => TextIO.output (bstream, bcstring))
		     in
			 (* do not perform rest of compilation *)
			 raise FINISHED
		     end
		else ()

        (* Output C code *)
        val () = Flag.guard Flags.flag_verbose
		 (fn () => say ("Writing library headers to " ^ path_concat (out_dir, hname) ^ " ...")) ()
        val () = SafeIO.withOpenOut
                 (path_concat (out_dir, hname))
                 (fn hstream =>
                  TextIO.output (hstream, PrintC.pp_program library_headers []))

        val () = Flag.guard Flags.flag_verbose
		 (fn () => say ("Writing C code to " ^ path_concat (out_dir, cname) ^ " ...")) ()
	val () = SafeIO.withOpenOut 
                 (path_concat (out_dir, cname))
                 (fn cstream =>
                  TextIO.output (cstream, PrintC.pp_program program
                                         [cc0_lib,
                                          !Flags.runtime ^ ".h",
                                          hname]))

        val absBaseDir = abspath (!Flags.base_dir)
        val runtimeDir = OS.Path.concat (absBaseDir, "runtime")

        val cflags = 
            " -std=c99 -g"
	    (* Oct 26, 2011, this allows C0 int to be represented as C int *)
            (* because two's-complement arithmetic is specified *)
            ^ " -fwrapv"
	    ^ (if Flag.isset Flags.flag_verbose then " -Wall -Wextra" else " -w")
            ^ " -o " ^ (!Flags.a_out)
            (* Dec 24, 2012, implements the -c flag *)
            ^ (if null (!Flags.gcc_args) then "" else " ")
            ^ String.concatWith " " (List.rev (!Flags.gcc_args))

        (* gcc command for linking with static libraries *)
	val gcc_static_lib_command = fn () =>
            "gcc"
            ^ cflags

            (* Location of cc0lib.h and <runtime>.h *)
	    ^ " -I" ^ path_concat (!Flags.base_dir, "include") 
	    ^ " -I" ^ path_concat (!Flags.base_dir, "runtime") 

            (* add lib and runtime directories to search path *)
            ^ " " ^ String.concatWith " " (map (fn p => "-L" ^ (abspath p)) (!Flags.search_path))
            ^ " -L" ^ (!Flags.base_dir ^ "/runtime")

            (* Finally, use the cc0main.c file *)
            ^ " " ^ path_concat3 (!Flags.base_dir, "lib", cc0_main)

            (* The actual c0 main file *)
            ^ " " ^ path_concat (out_dir, cname)

            (* C0 librarires *)
            ^ " " ^ String.concatWith " " (map (fn l => "-l" ^ l) (!Flags.libraries))
            (* Link C0 runtime *)
            ^ " -l" ^ !Flags.runtime
            (* Link libpng if necessary *)
            ^ (if List.exists (fn l => l = "img") (!Flags.libraries) then " -lpng" else "")
            (* Link gc if needed *)
            ^ (if !Flags.runtime <> "bare" then " -lgc" else "")

        (* Invoke GCC *)
        (* gcc command for linking with dynamic libraries *)
        val gcc_dynamic_lib_command = fn () =>
            "gcc"
            ^ cflags

            (* Location of cc0lib.h and <runtime>.h *)
	    ^ " -I" ^ path_concat (!Flags.base_dir, "include") 
	    ^ " -I" ^ path_concat (!Flags.base_dir, "runtime") 

            (* The actual c0 main file *)
            ^ " " ^ path_concat (out_dir, cname)

            (* Finally, use the cc0main.c file *)
            ^ " " ^ path_concat3 (!Flags.base_dir, "lib", cc0_main)

            (* Now use the libraries (<source>.h) and code (<source>.c) *)
            ^ " " ^ String.concatWith " " (map (fn p => "-Wl,-rpath " ^ (abspath p)) (!Flags.search_path))
            ^ " " ^ String.concatWith " " (map (abspath o get_library_archive) (!Flags.libraries))

            (* Use the runtime and cc0lib *)
            ^ " -L" ^ (!Flags.base_dir ^ "/runtime")
            ^ " -Wl,-rpath " ^ runtimeDir
            ^ " " ^ (abspath (path_concat (runtimeDir, native_lib_name (!Flags.runtime))))

        val gcc_command = (if Flag.isset Flags.flag_static then 
                             gcc_static_lib_command ()
                           else
                             gcc_dynamic_lib_command ())

        val () = Flag.guard Flags.flag_verbose (fn () => say ("% " ^ gcc_command)) ()
        val status = OS.Process.system gcc_command
	val () = Flag.guard Flags.flag_verbose
		(fn () => say (if OS.Process.isSuccess status then "succeeded" else "failed")) ()

        val () = if Flag.isset Flags.flag_save_files then ()
                 else ( Flag.guard Flags.flag_verbose (fn () => say ("Deleting " ^ cname)) ()
		      ; OS.FileSys.remove (path_concat (out_dir, cname))
		      ; Flag.guard Flags.flag_verbose (fn () => say ("Deleting " ^ hname)) ()
		      ; OS.FileSys.remove (path_concat (out_dir, hname)) )

        val status =
	    if Flag.isset Flags.flag_exec
	    then let val exec_command =
			 OS.Path.joinDirFile {dir=OS.Path.currentArc,
					      file=(!Flags.a_out)}
                     val exec_with_args = 
                         String.concatWith " " 
                            (exec_command :: rev (!Flags.runtime_args))
		     val () = Flag.guard Flags.flag_verbose
		              (fn () => say ("% " ^ exec_with_args)) ()
		 in
		     OS.Process.system exec_with_args
		 end
	    else status

      in
	  status
      end
      handle ErrorMsg.Error => ( say "Compilation failed" ; OS.Process.failure )
	   | EXIT => OS.Process.failure
	   | FINISHED => OS.Process.success
           | e => ( say ("Unexpected exception in cc0:\n" ^ exnMessage e ^ "\n")
                  ; if false (* true: development mode, false: production *)
                    then raise e
                    else OS.Process.failure)
           (* foldr (fn (a,b) => a ^ "\n" ^ b) "" (SMLofNJ.exnHistory e) *)
           (* Above extra bits commented out by Rob, Nov 15 2012. 
            * The compiler needs to compile with MLton! - Rob *)

  fun test s = main ("", String.tokens Char.isSpace s)

end
