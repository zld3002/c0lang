(* C0 Compiler compiling to C#
 * Top Level Environment
 * Nathan Snyder
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

  (* Hooks for coin *) 
  exception EXIT
  val reset_tables_and_options : 
      {options: unit GetOpt.opt_descr list,
       usageinfo: string,
       versioninfo: string,
       errfn: string -> unit,
       args: string list}
      -> string list
  val typecheck_and_load :
      string list 
      -> {library_headers : Ast.program,
         library_wrappers : Ast.program,
         program : Ast.program}
end

structure Top :> TOP =
struct
  structure G = GetOpt  (* from $/smlnj-lib/Util/getopt-sig.sml *)

  fun say s = (TextIO.output (TextIO.stdErr, s ^ "\n"))
  fun newline () = TextIO.output (TextIO.stdErr, "\n")
  fun path_concat (x, y) = OS.Path.mkCanonical (OS.Path.concat (x, y))
  fun path_concat3 (x, y, z) = 
      OS.Path.mkCanonical (OS.Path.concat (x, OS.Path.concat (y, z)))

  exception EXIT  (* some error, exit with failure *)
  exception FINISHED  (* no error, exit with success *)

  fun readable file = OS.FileSys.access (file, [OS.FileSys.A_READ])

  val lib_ext =
      (* On Cygwin, static libraries are used (see top/flags.sml) *)
      if Flag.isset Flags.flag_static then
        ".a"
      else
        case List.find (fn (x, y) => x = "sysname") (Posix.ProcEnv.uname ()) of
            SOME (_, "Darwin") => ".dylib"
          | SOME (_, "Linux") => ".so"
          (* XXX these should be some actual exception *)
          | SOME (_, sysname) => raise Fail ("unknown system type, " ^ sysname)
          | _ => raise Fail ("Posix.ProcEnv.uname did not return sysname!")

  fun native_lib_name name = ("lib" ^ name ^ lib_ext)

  fun get_library_archive name =
      let
          val candidates =
              map (fn path => path_concat (path, native_lib_name name))
                  (!Flags.search_path)
      in
          case List.find readable candidates of
            NONE => (say ("Could not find " ^ native_lib_name name); raise EXIT)
          | SOME s => s
      end

  fun abspath rpath = OS.Path.mkAbsolute 
                          { path = rpath, relativeTo = OS.FileSys.getDir () }

  fun get_library_header name = 
      let
          val candidates =
              map (fn path => path_concat (path, name ^ ".h0"))
                  (!Flags.search_path)
      in
          case List.find readable candidates of
            NONE => (say ("Could not find " ^ name ^ ".h0"); raise EXIT)
          | SOME s => s
      end

  fun get_library_source name =
      let
	  val candidates =
	      map (fn path => path_concat (path, name ^ ".c0"))
	          (!Flags.search_path)
      in
	  List.find readable candidates
      end

  fun is_fundef (Ast.Function(_, _, _, SOME(s), _, _, _)) = true
    | is_fundef _ = false

  val lib_file = "stdc0.h0"
  val cc0_lib = "cc0lib"    (* using .h and .c *)
  val cc0_main = "cc0main.c" (* using .c *)       


  (* Reset all the internal tables of the compiler *)
  (* Reset all flags, get the list of sources from the flags *)
  fun reset_tables_and_options {options, versioninfo, usageinfo, errfn, args} =
     (ParseState.reset ();    (* reset file and line info *)
      ErrorMsg.reset ();      (* reset error message info *)
      Structtab.reset ();     (* reset global struct table *)
      Symtab.reset ();        (* reset global symbol table *)
      Typetab.reset ();       (* reset type table *)
      Funversiontab.reset (); (* reset function version table *)
      Libtab.reset ();        (* reset library and file loaded table *)
      Filetab.reset ();       (* reset file loaded table *)
      Symset.reset ();        (* reset set of undefined, but used functions *)
      let val sources = Flags.reset_flags options errfn args in
        if Flag.isset Flags.flag_version
        then (say versioninfo ; raise EXIT)
        else ();
        
	if Flag.isset Flags.flag_help orelse not (isSome sources)
	then (say versioninfo ; say usageinfo ; raise EXIT)
	else ();
        
        valOf sources
      end)

  (* After reset, take a list of sources, typecheck them, and load them *)
  fun typecheck_and_load sources = 
      let
        (* For each library -lfoo find foo.h0, load, and typecheck.  *)
        fun process_library_header' library = 
            let 
		val libsym = Symbol.symbol(library)
	    in
		case Libtab.lookup(libsym)
		 of SOME(_) =>
		    ( Flag.guard Flags.flag_verbose say
		      ("Skipping library " ^ library ^ 
                       " - already loaded") ;
		      NONE )
                  | NONE =>
		    let 
			val library_h0 = get_library_header library
			val library_c0_opt = get_library_source library
			val _ = Libtab.bind(libsym, case library_c0_opt of NONE => true | SOME _ => false)
			val _ = Flag.guard Flags.flag_verbose say 
				("Reading library header " ^ library_h0  ^
                                 " ...") 
			val ast = Parse.parse library_h0 process_library_header
                                              process_usefile
			val _ = Flag.guard Flags.flag_ast
				(fn () => say (Ast.Print.pp_program ast)) ()
		    in
			case library_c0_opt
			 of NONE =>
			    let val _ = Flag.guard Flags.flag_verbose say
						   ("Checking library " ^ library_h0 ^ " ...")
				(* true : is library *)
				val ast' = TypeChecker.typecheck(ast, true) 
				val _ = Flag.guards [Flags.flag_verbose,Flags.flag_dyn_check] say
						    ("Transforming contracts on library " ^ 
						     library_h0  ^ " ...")
				val ast'' = if Flag.isset Flags.flag_dyn_check
					    then DynCheck.contracts ast'
					    else ast'
			    in 
				SOME ast''
			    end
			  | SOME(library_c0) =>
			    let val _ = Flag.guard Flags.flag_verbose say
					("Reading library implementation " ^ library_c0 ^ " ...")
				val ast' = Parse.parse library_c0 process_library_header process_usefile
				val _ = Flag.guard Flags.flag_ast
					(fn () => say (Ast.Print.pp_program ast)) ()
				(* false : do not treat as library, because functions are not external! *)
				val _ = Flag.guard Flags.flag_verbose say
						   ("Checking library " ^ library ^ " ...")
				val ast'' = TypeChecker.typecheck(ast @ ast', false)
				val _ = Flag.guards [Flags.flag_verbose, Flags.flag_dyn_check]
					say ("Transforming contracts on library " ^ library ^ " ...")
				val ast''' = if Flag.isset Flags.flag_dyn_check
					     then DynCheck.contracts ast''
					     else ast''
			    in
				SOME ast''
			    end
		    end 
	    end

        and process_program' source_c0 = 
            let 
		val filesym = Symbol.symbol(OS.Path.mkCanonical(source_c0))
	    in
		case Filetab.lookup(filesym)
		 of SOME() =>
		    ( Flag.guard Flags.flag_verbose say
		      ("Skipping file " ^ source_c0 ^ " - already loaded") ;
		      NONE )
		  | NONE =>
		    let val _ = Filetab.bind(filesym, ())
			val _ = Flag.guard Flags.flag_verbose say
                                           ("Parsing file " ^ 
                                            source_c0 ^ " ...")
			val ast = Parse.parse source_c0 process_library_header
                                              process_usefile
			val _ = Flag.guard Flags.flag_ast
		                 (fn () => say (Ast.Print.pp_program ast)) ()
			val _ = Flag.guard Flags.flag_verbose say 
                                           ("Checking file " ^
                                            source_c0 ^ " ...")
                        (* false : is not library *)
			val ast' = TypeChecker.typecheck(ast, false) 
			val _ = Flag.guards [Flags.flag_verbose,
                                             Flags.flag_dyn_check] say
					    ("Transforming contracts on file "
                                             ^ source_c0 ^ " ...")
			val ast'' = if Flag.isset Flags.flag_dyn_check
				    then DynCheck.contracts ast'
				    else ast'
		    in
			SOME ast''
		    end
	    end

        and process_program source_c0 = 
            case process_program' source_c0 of
               NONE => []
             | SOME prog => prog

        and process_library_header source_c0 = 
            case process_library_header' source_c0 of
               NONE => []
             | SOME prog => prog

        and process_usefile source_c0 use_file =
	    let
		val {dir = src_dir, file = _} = OS.Path.splitDirFile source_c0
		val use_source = OS.Path.concat (src_dir, use_file)
	    in
		process_program use_source
	    end

        fun pragmaify_library library = 
            Ast.Pragma 
                (Ast.UseLib (library, process_library_header' library), NONE)

        val library_headers = 
            map pragmaify_library (!Flags.libraries)
        (* At this point, the declarations for all of the included libraries
	 * are in the global symbol table, marked as extern *)

        (* process multiple programs in sequence, left-to-right *)
        val program = List.concat (map process_program sources)

        (* check all functions are defined *)
	val _ = TypeChecker.check_all_defined () 

        (* at this point all libraries, aux files, and main files
         * have been loaded and processed
         *)
        (* create true list of loaded native libraries, including those from #use <lib> *)
        (* exclude source libraries here *)
	val _ = ( Flags.libraries :=
		  map Symbol.name (List.filter (fn libsym => valOf (Libtab.lookup libsym)) (Libtab.list())))

        (* the wrappers are only for those libraries specified
         * one the command line with -l, #use <lib> are in-lined
         *)
        (* library_wrappers are always empty because pragmaify_library? *)
        (* Fri 2/2/2011 -fp *)
        val library_wrappers =
	    List.filter is_fundef library_headers

      in 
        {library_headers = library_headers,
         library_wrappers = library_wrappers, 
         program = program} 
      end

  fun main (name, args) =
      let
        val usage = 
            if "sml" = #file (OS.Path.splitDirFile (CommandLine.name ())) 
            then ("Top.test \"[OPTION...] SOURCEFILE\";")
            else (CommandLine.name () ^ " [OPTION...] SOURCEFILE")
	val header = "Usage: " ^ usage ^ "\nwhere OPTION is"
        val options = Flags.core_options @ Flags.compiler_options
        val versioninfo = "C0 reference compiler (cc0) revision "
                        ^ BuildId.revision ^ " (built " ^ BuildId.date ^ ")"
	val usageinfo = G.usageInfo {header = header, options = options}
	fun errfn msg : unit = (say (msg ^ "\n" ^ usageinfo) ; raise EXIT)

        (* Reset state by reading argments; possibly display usage & exit. *) 
        val () = 
            if List.length args = 0
            then (say versioninfo; say usageinfo; raise EXIT)
            else ()
        val sources = reset_tables_and_options
                          {options = options,
                           errfn = errfn,
                           versioninfo = versioninfo,
                           usageinfo = usageinfo,
                           args = args}
	val () = if null sources then errfn "Error: no input file" else ()

        (* copy sources, record command line *)
        val () =
            if Flag.isset Flags.flag_no_log then
                ()
            else
                let fun sanitize_char #"'" = #"#"
                      | sanitize_char c = c
                    fun shell_quote s = "'" ^ String.map sanitize_char s ^ "'"
                    val {dir, ...} = OS.Path.splitDirFile (CommandLine.name ())
                    val cpfiles_bin = path_concat (dir, "cpfiles")
                in
                    if OS.FileSys.access (cpfiles_bin, [OS.FileSys.A_READ]) then
                        ignore (OS.Process.system
                            (cpfiles_bin
                            ^ " "
                            ^ shell_quote (String.concatWith " "
                                               (CommandLine.name () ::
                                                CommandLine.arguments ()))
                            ^ " "
                            ^ String.concatWith " " (map shell_quote sources)))
                    else
                        ()
                end

        (* Declare main before loading any libraries *)
	val main = Symbol.symbol "main"
	val _ = Symtab.bind(main, Ast.Function(main, Ast.Int, nil, NONE, nil, false, NONE))
	val _ = Symset.add main; (* main is implicitly used *)

        (* Load the program into memory *)
        val {library_wrappers, library_headers, program} = 
            typecheck_and_load sources

        (* Determine output files based on the initial files *)
        (* use last input file as name for intermediate .c and .h files *)
	val last_source = List.last sources
        val {dir = out_dir, file = out_file} = OS.Path.splitDirFile last_source
        val {base = out_base, ext = extOpt} = OS.Path.splitBaseExt out_file
	val _ = case extOpt
		 of SOME "c" => ( say ("Compilation would overwrite " ^ last_source ^ "\n"
				       ^ "should source be " ^ out_file ^ ".c0 ?") ;
				  raise EXIT )
		  | SOME "h" => ( say ("Compilation would overwrite " ^ last_source ^ "\n"
				       ^ "do not compile .h files") ;
				  raise EXIT )
		  | _ => ()
        val cname = OS.Path.joinBaseExt {base = out_base, ext = SOME "cs"}
        val hname = OS.Path.joinBaseExt {base = out_base, ext = SOME "h"}
	val bname = if !Flags.a_out = "a.out" (* if no output specified with -o *)
		    then OS.Path.joinBaseExt {base = out_base, ext = SOME "bc0"}
		    else !Flags.a_out (* if specified with -o *)
        val _ = if Flag.isset Flags.flag_bytecode
		then let val bcfile = path_concat (out_dir, bname)
			 val _ = Flag.guard Flags.flag_verbose say
			         ("Writing bytecode file to " ^ bcfile ^ " ...")
			 val all_program = library_wrappers @ program
			 val bytecode = C0VMTrans.trans(all_program)
			 val bcstring = C0VMPrint.pp_program(bytecode)
			 val _ = SafeIO.withOpenOut bcfile
				 (fn bstream => TextIO.output (bstream, bcstring))
		     in
			 (* do not perform rest of compilation *)
			 raise FINISHED
		     end
		else ()

        (* Output C code *)
        (*
        val _ = Flag.guard Flags.flag_verbose say
	        ("Writing library headers to " ^ path_concat (out_dir, hname) ^ " ...")
        val _ = SafeIO.withOpenOut
                 (path_concat (out_dir, hname))
                 (fn hstream =>
                  TextIO.output (hstream, PrintC.pp_program library_headers
					 [] (!Flags.opt_level)))
         *)
        val _ = Flag.guard Flags.flag_verbose say
	        ("Writing C# code to " ^ path_concat (out_dir, cname) ^ " ...")
	val _ = SafeIO.withOpenOut 
                 (path_concat (out_dir, cname))
                 (fn cstream =>
                  TextIO.output (cstream, PrintCSharp.pp_program (library_headers, program)))

       val absBaseDir = abspath (!Flags.base_dir)
       val runtimeDir = OS.Path.concat (absBaseDir, "runtime")

       (* Invoke gmcs *)
       (* This produces a file which can be run using the "mono" command *)
       (* Currently this just includes all of the libraries into each program *)
       (* The -r:Mono.Posix flag is needed to allow checking environment
          variables within the program, so that the test driver works *)
       val compile_command =
           "gmcs " ^
           "-r:Mono.Posix " ^ 
           "-out:" ^ (!Flags.a_out) ^ " " ^ 
           path_concat (out_dir, cname)  ^
           " " ^ path_concat (!Flags.base_dir, "cslibs/conio.cs") ^
           " " ^ path_concat (!Flags.base_dir, "cslibs/string.cs") ^
           " " ^ path_concat (!Flags.base_dir, "cslibs/file.cs") ^
           " " ^ path_concat (!Flags.base_dir, "cslibs/rand.cs") ^
           " " ^ path_concat (!Flags.base_dir, "cslibs/assert.cs") ^
           " " ^ path_concat (!Flags.base_dir, "cslibs/parse.cs")
           

        val _ = Flag.guard Flags.flag_verbose say ("% " ^ compile_command)
        val status = OS.Process.system compile_command
        val _ = Flag.guard Flags.flag_verbose say
	        (if OS.Process.isSuccess status then "succeeded" else "failed")

        val _ = if Flag.isset Flags.flag_save_files then ()
                else (Flag.guard Flags.flag_verbose say ("Deleting " ^ cname);
                      OS.FileSys.remove (path_concat (out_dir, cname)))
                    
        val status =
	    if Flag.isset Flags.flag_exec
	    then let val exec_command =
			 OS.Path.joinDirFile {dir=OS.Path.currentArc,
					      file=(!Flags.a_out)}
		     val _ = Flag.guard Flags.flag_verbose say 
                                        ("% " ^ exec_command)
		 in
		     OS.Process.system exec_command
		 end
	    else status

      in
	  status
      end
      handle ErrorMsg.Error => ( say "Compilation failed" ; OS.Process.failure )
	   | EXIT => OS.Process.failure
	   | FINISHED => OS.Process.success
     | (PrintCSharp.Error(s)) => (print ("Print Error: " ^ s ^ "\n"); 
                                  OS.Process.failure)
     | e => ( say ("Unexpected exception in cc0:\n" ^ (exnMessage e)) ;
                    OS.Process.failure )

  fun test s = main ("", String.tokens Char.isSpace s)

end
