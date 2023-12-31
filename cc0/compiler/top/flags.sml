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
  val flag_static_check : Flag.flag
  val flag_purity_check : Flag.flag
  val flag_verif_check : Flag.flag
  val flag_warn : Flag.flag
  val flag_save_files : Flag.flag
  val flag_exec : Flag.flag
  val flag_bytecode : Flag.flag
  val flag_bytecode_ext : Flag.flag
  val flag_static : Flag.flag
  val flag_only_typecheck : Flag.flag

  val base_dir : string ref
  val search_path : string list ref
  val libraries : string list ref
  val gcc_args : string list ref
  val runtime_args : string list ref
  val runtime : string ref
  val standard : string option ref
  val a_out : string ref
  val bytecode_arch : int ref

  (* Only for the coin interpreter *)
  val flag_trace : Flag.flag 
  val flag_print_codes : Flag.flag

  (* Only for the codex debugger *)
  val flag_interactive : Flag.flag
  val flag_emacs : Flag.flag
  val run_call : string option ref

  (* Compiler warning test *)
  val warning_enabled : string -> bool 

  val core_options : unit GetOpt.opt_descr list
  val coin_options : unit GetOpt.opt_descr list
  val compiler_options : unit GetOpt.opt_descr list
  val codex_options : unit GetOpt.opt_descr list

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
  val flag_static_check = Flag.flag "static-check"
  val flag_purity_check = Flag.flag "purity-check"
  val flag_verif_check = Flag.flag "verif-check"
  val flag_warn = Flag.flag "warn" (* Indentation warnings *)
  val flag_save_files = Flag.flag "save-files"
  val flag_exec = Flag.flag "exec"
  val flag_bytecode = Flag.flag "bytecode"
  val flag_bytecode_ext = Flag.flag "bytecode-ext"
  val flag_static = Flag.flag "static"
  val flag_only_typecheck = Flag.flag "only-typecheck"
  
  val base_dir = ref ""                       (* see reset_flags ()           *)
  val search_path : string list ref = ref []  (* Search path for libraries    *)
  val libraries : string list ref = ref []    (* Desired libraries            *)
  val runtime_args : string list ref = ref [] (* Arguments for runtime        *)
  val gcc_args : string list ref = ref []     (* Arguments for gcc            *)
  val runtime  = ref ""                       (* Runtime (bare, c0rt, unsafe) *)
  val standard : string option ref = ref NONE (* Language standard (l1, c0)   *)
                                              (* Default is to use extension  *)
  val a_out = ref ""                          (* Output executable            *)
  val bytecode_arch = ref 64                  (* Architecture for bytecode    *)
  val warnings : string list ref = ref []     (* Compiler warnings (e.g. "unreachable-code") *)

  val flag_trace = Flag.flag "trace"
  val flag_print_codes = Flag.flag "print_codes"

  val flag_interactive = Flag.flag "interactive"
  val flag_emacs = Flag.flag "emacs"
  val run_call : string option ref = ref NONE (* function call to make; internal default is main() *)

  local
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

          (* decide if static or dynamic libraries should be used *)
          case List.find (fn (x, y) => x = "sysname") (Posix.ProcEnv.uname ()) of
              SOME (_, id) => if String.isPrefix "CYGWIN" id then Flag.set flag_static else () 
            | _ => raise Fail ("Posix.ProcEnv.uname did not return sysname!");

          (* Unset all flags *)
          List.app Flag.unset [flag_verbose, flag_help,
                               flag_version, flag_no_log,
                               flag_ast, flag_dyn_check, flag_exec, flag_bytecode, 
                               flag_bytecode_ext,
                               flag_static_check, flag_verif_check,
                               flag_warn, flag_save_files,
                               flag_trace, flag_print_codes];
          (* Set default flags *)
          List.app Flag.set [flag_purity_check];

          (* Set other defaults *)
          libraries := []; runtime := "c0rt"; a_out := "a.out";
          standard := NONE;
          runtime_args := []; gcc_args := [];
          bytecode_arch := 64;
          SOME (#2 (GetOpt.getOpt {argOrder = GetOpt.Permute,
                                   options = options,
                                   errFn = errfn}
                                  args))
          handle Domain => 
                 (errfn "Integer option incorrect or out of range"; NONE)
                 (* re-raise EXIT exception from top.sml *)

      end
  
  val known_warnings = [
    "unreachable-code",
    "unused-variable",
    "unused-expression"
  ]

  fun warning_enabled s = 
    Option.isSome (List.find (fn f => s = f) (!warnings))

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
(* Disabled temporarily to create Spring 2012 binaries *)
(* December 30, 2012 -rjs *)
(*
     {short = "S", long=["static-check"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_static_check),
      help="Check contracts and safety statically"},
     {short = "", long=["verif-check"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_verif_check),
      help="Enable verification condition checking"},
*)
     {short = "", long=["no-purity-check"],
      desc=GetOpt.NoArg (fn () => Flag.unset flag_purity_check),
      help="Disable checking contract functions for purity"},
     {short = "l", long=["library"],
      desc=GetOpt.ReqArg ((fn (s) => (libraries := s :: !libraries)), "<lib>"),
      help="Include the library <lib>"},
     {short = "L", long=[],
      desc=GetOpt.ReqArg
               ((fn (s) => (search_path := !search_path @ [ s ])),"<dir>"),
      help="Add <dir> to the search path for libraries"},
     {short = "a", long=[],
      desc=GetOpt.ReqArg 
              ((fn (s) => (runtime_args := s :: !runtime_args)), "<arg>"),
      help="Pass an argument to the executing C0 program"},
     {short = "", long=["standard"],
      desc=GetOpt.ReqArg ((fn (s) => (standard := SOME s)), "<std>"),
      help="Force language std. (ie c0), ignoring extension"},
     {short = "V", long=["version"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_version),
      help="Print version number and compile info"},
     {short = "n", long=["no-log"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_no_log),
      help="Disable logging for this compile"},
      (* Nov 2019 *)
      {short = "W", long=[],
      desc=GetOpt.OptArg (
              (fn NONE => warnings := known_warnings
                | SOME "all" => warnings := known_warnings
                | SOME "none" => warnings := []
                | SOME s => (case List.find (fn f => s = f) known_warnings of 
                              SOME _ => warnings := s :: !warnings 
                            | NONE => ErrorMsg.error NONE ("unknown warning '" ^ s ^ "'"))),
              "warning"), 
      help="Enable warning/warning group"}]

  val coin_options : unit GetOpt.opt_descr list = 
    [{short = "t", long=["trace"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_trace),
      help="Trace execution of interpreted code"},
     {short = "", long=["print-codes"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_print_codes),
      help="Print out the internal language's representation"}]

  val codex_options : unit GetOpt.opt_descr list = 
    [{short = "i",long=["interactive"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_interactive),
      help="Run codex in interactive (command-line) mode"},
     {short = "e",long=["emacs"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_emacs),
      help="Run in mode compatible with emacs plugin"},
     {short = "r",long=["run"],
      desc=GetOpt.ReqArg ((fn (s) => (run_call := SOME(s))), "<call>"),
      help="Function call to start with (default: 'main()')"}]
    
  val compiler_options : unit GetOpt.opt_descr list = 
    [{short = "", long=["dump-ast"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_ast),
      help="Pretty print the program's abstract syntax tree"},
     {short = "s", long=["save-files"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_save_files),
      help="Save .c and .h files produced by the compiler"},
     {short = "r", long=["runtime"],
      desc=GetOpt.ReqArg ((fn (s) => (runtime := s)), "<rt>"),
      help="Select a runtime (default 'c0rt')"},
     {short = "b", long=["bytecode"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_bytecode),
      help="Generate bytecode instead of executable"},
     {short = "", long=["bytecode-ext"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_bytecode_ext),
      help="Generate bytecode annotated with source extents"},
     {short = "m", long=["bc-arch"],
      desc=GetOpt.ReqArg ((fn (s) => (bytecode_arch := parse_bytecode_arch s)), "<arch>"),
      help="Set bytecode architecture: 64 (default) or 32"},
     {short = "o", long=["output"],
      desc=GetOpt.ReqArg ((fn (s) => (a_out := s)), "<file>"),
      help="Place the executable output into <file>"},
     {short = "c", long=[],
      desc=GetOpt.ReqArg 
              ((fn (s) => (gcc_args := s :: !gcc_args)), "<arg>"),
      help="Pass an argument to the C compiler"},
     {short = "w", long=["warn"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_warn),
      help="Warn about style issues in the code"},
     {short = "x", long=["exec"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_exec),
      help="Execute compiled file"},
     {short = "", long=["only-typecheck"],
      desc=GetOpt.NoArg (fn () => Flag.set flag_only_typecheck),
      help="Stop after typechecking"}]

  end (* local *)

end
