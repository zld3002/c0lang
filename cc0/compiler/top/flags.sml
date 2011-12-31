(* C0 Compiler
 * Flags
 * Rob Simmons
 *)

signature FLAGS = sig
  val flag_verbose : Flag.flag
  val flag_help : Flag.flag
  val flag_no_log : Flag.flag
  val flag_version : Flag.flag
  val flag_ast : Flag.flag
  val flag_dyn_check : Flag.flag
  val flag_save_files : Flag.flag
  val flag_exec : Flag.flag
  val flag_bytecode : Flag.flag 
  val opt_level : int ref
  val base_dir : string ref
  val search_path : string list ref
  val libraries : string list ref
  val runtime : string ref
  val a_out : string ref
  val bytecode_arch : int ref

  (* Only for the coin interpreter *)
  val flag_trace : Flag.flag 
  val flag_print_codes : Flag.flag


  val core_options : unit GetOpt.opt_descr list
  val coin_options : unit GetOpt.opt_descr list
  val compiler_options : unit GetOpt.opt_descr list

  val reset_flags : unit GetOpt.opt_descr list (* Options *)
                    -> (string -> unit)        (* Error function *)
                    -> string list             (* List of arguments *)
                    -> string list option      (* List of source files *)
end

structure Flags :> FLAGS = struct

  (* see flag explanations below *)
  val flag_verbose = Flag.flag "verbose"
  val flag_help = Flag.flag "help"
  val flag_no_log = Flag.flag "no-log"
  val flag_version = Flag.flag "version"
  val flag_ast = Flag.flag "ast"
  val flag_dyn_check = Flag.flag "dyn-check"
  val flag_save_files = Flag.flag "save-files"
  val flag_exec = Flag.flag "exec"
  val flag_bytecode = Flag.flag "bytecode"
  val opt_level = ref 0		(* default is opt level 0 *)

  val base_dir = ref ""                       (* see reset_flags ()        *)
  val search_path : string list ref = ref []  (* Search path for libraries  *)
  val libraries : string list ref = ref []    (* Desired libraries          *)
  val runtime  = ref ""                       (* Runtime (bare, c0rt, unsafe) *)
  val a_out = ref ""                          (* Output executable *)
  val bytecode_arch = ref 64		      (* Architecture for bytecode *)

  val flag_trace = Flag.flag "trace"
  val flag_print_codes = Flag.flag "print_codes"

  local
    fun parse_opt_level (s) =
        (case Int.fromString(s)
	  of SOME(opt) => opt
	   | NONE => raise Domain)  (* Domain ??? *)

    fun parse_bytecode_arch s = case Int.fromString s of
           SOME(32) => 32
	 | SOME(64) => 64
	 | SOME(n) => raise Domain (* Domain ??? *)
	 | NONE => raise Domain

  in

  (* Determines the default base directory at runtime, sets defaults. *)
  fun reset_flags options (errfn : string -> unit) (args : string list) =
      let
          val {dir, file} = OS.Path.splitDirFile (CommandLine.name ())
      in
          (* In the SML/NJ toplevel, use current directory. *)
          if file = "sml" then base_dir := "."
          (* In a precompiled binary, use parent of executable's directory. *)
          else base_dir := OS.Path.mkCanonical (OS.Path.getParent dir);

          (* Set default search path using base_dir *)
          search_path := 
          [ OS.Path.mkCanonical (OS.Path.concat (!base_dir, "lib")) ];

          (* Unset all flags *)
          List.app Flag.unset [flag_verbose, flag_help,
                               flag_version, flag_no_log,
			       flag_ast, flag_exec, flag_bytecode,
                               flag_save_files, flag_trace, flag_print_codes];

          (* Set other defaults *)
          opt_level := 0; libraries := []; runtime := "c0rt"; a_out := "a.out";
	  bytecode_arch := 64;
          SOME (#2 (GetOpt.getOpt {argOrder = GetOpt.Permute,
		                   options = options,
		                   errFn = errfn}
		                  args))
          handle Domain => 
                 (errfn "Cannot parse optimization level as integer"; NONE)
               | _ => 
                 (errfn "Error parsing command-line options"; NONE)
      end

  val core_options : unit GetOpt.opt_descr list = 
    [{short = "v", long=["verbose"], 
      desc=GetOpt.NoArg (fn () => Flag.set flag_verbose),
      help="Give verbose status and error messages"},
     {short = "h", long=["help"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_help),
      help="Give short usage message and exit"},
     {short = "d", long=["dyn-check"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_dyn_check),
      help="Check contracts dynamically"},
     {short = "l", long=["library"],
      desc=GetOpt.ReqArg ((fn (s) => (libraries := s :: !libraries)), "<lib>"),
      help="Include the library <lib>"},
     {short = "L", long=[],
      desc=GetOpt.ReqArg
               ((fn (s) => (search_path := !search_path @ [ s ])),"<dir>"),
      help="Add <dir> to the search path for libraries"},
     {short = "V", long=["version"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_version),
      help="Print version number and compile info"}]

  val coin_options : unit GetOpt.opt_descr list = 
    [{short = "t", long=["trace"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_trace),
      help="Trace execution of interpreted code"},
     {short = "", long=["print-codes"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_print_codes),
      help="Print out the internal language's representation"}]
    
  val compiler_options : unit GetOpt.opt_descr list = 
    [{short = "", long=["dump-ast"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_ast),
      help="Pretty print the program's abstract syntax tree"},
     {short = "s", long=["save-files"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_save_files),
      help="Save the .c and .h files produced by the compiler"},
     {short = "r", long=["runtime"],
      desc=GetOpt.ReqArg ((fn (s) => (runtime := s)), "<rt>"),
      help="Select a runtime (default \"c0rt\")"},
     {short = "O", long=["optimize"],
      desc=GetOpt.ReqArg 
               ((fn (s) => (opt_level := parse_opt_level(s))), "<opt>"),
      help="Optimize to level <opt> (default 0, >0 may be unsound)"},
     {short = "b", long=["bytecode"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_bytecode),
      help="Generate bytecode instead of executable"},
     {short = "m", long=["bytecode-arch"],
      desc=GetOpt.ReqArg ((fn (s) => (bytecode_arch := parse_bytecode_arch s)), "<arch>"),
      help="Generate bytecode for architecture <arch>, 64 or 32 (default 64)"},
     {short = "o", long=["output"],
      desc=GetOpt.ReqArg ((fn (s) => (a_out := s)), "<file>"),
      help="Place the executable output into <file>"},
     {short = "n", long=["no-log"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_no_log),
      help="Disable logging for this compile"},
     {short = "x", long=["exec"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_exec),
      help="Execute compiled file"}]

  end (* local *)

end
