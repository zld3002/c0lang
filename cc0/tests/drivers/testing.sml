signature TESTING = sig

  val go : string list -> OS.Process.status

end

signature TEST_IMPL = sig

  type result

  val result_to_string : result -> string

  val did_return : Word32.word option -> result -> bool
  val did_segfault : result -> bool
  val did_div_by_zero : result -> bool
  val did_abort : result -> bool
  val did_infloop : result -> bool
  val did_error : result -> bool (* Compiler error *)
  val did_failure : result -> bool (* EXIT_FAILURE *)

  (* The "string list" is a list of files that are suitable
   * for opening relative to the current directory or options
   * that will be interpreted by the driver (e.g., -l <lib>,
   * -d). *)
  val test      : string list -> result

  val args_desc : string
  val name : unit -> string
  datatype pred = LIB | TYPECHECK | GC | SAFE
  val matches_pred : pred -> bool

  (* HACKS *)
  val set_name : string -> unit

end

functor Testing (Impl : TEST_IMPL) :> TESTING = struct

  exception Skip
  exception Error of string
  val base_path = ref "" 

  val line    = ref 0
  val skipped = ref 0
  val timeout = ref 0
  val errors  = ref 0
  val success = ref 0
  val failure = ref 0
  val error_tests  : string list ref = ref []
  val failed_tests : string list ref = ref []

  fun name () = CommandLine.name ()

  fun helpful_message () = let val p = fn s => print (s ^ "\n") in
p("Usage: " ^ name () ^ " " ^ Impl.args_desc ^ "<filename> [ <filename> ... ]");
p("Each <filename> should be either a .c0 file that potentially starts with a");
p("line \"//<spec>\" or else a config file where each line takes the form"); 
p("\"<spec> - <filename> [ <filename> ... ]\".");
p("See the tests/README file for a description of the syntax of <spec>.");
OS.Process.failure
end


  fun n num = 
    let in
      if String.sub (num,0) = #"-"
      then Word32.~ 
             (valOf (Word32Signed.fromString (String.extract (num, 1, NONE))))
      else valOf (Word32Signed.fromString num)
    end handle _ => raise Error "Syntax error in config file (bad integer)..."

  (* From Tom's sml-lib *)
  fun K x y = x

  fun pad' c n s =
    if (size s >= n) then (s, "")
    else (s, (implode (List.tabulate (n - size s, K c))))

  fun padex c n s = 
    if n < 0 then
        let val (a, b) = pad' c (~ n) s
        in b ^ a
        end
    else
        let val (a, b) = pad' c n s
        in a ^ b
        end

  val pad = padex #" "

  (* support a subset of cc0 options -- this is just used for parsing the
     compiler arguments, so no docstrings are provided *)
  fun reqarg opt = GetOpt.ReqArg (fn s => opt ^ s, "")
  fun noarg opt = GetOpt.NoArg (fn () => opt)
  val options =
    [{short = "l", long=["library"], desc = reqarg "-l", help=""},
     {short = "L", long=[], desc = reqarg "-L", help=""},
     {short = "d", long=["dyn-check"], desc = noarg "-d", help=""},
     {short = "", long=["no-purity-check"], desc = noarg "--no-purity-check", help=""}]

  fun check_readable filename =
    (* i think this is slightly saner --wjl *)
    let
      val path = OS.Path.mkAbsolute {path = filename, relativeTo = !base_path}
    in
        if OS.FileSys.access (path, [OS.FileSys.A_READ])
        then path
        else raise Error ("File " ^ filename ^
                          " does not exist or is not readable")
    end

  fun chk args =
    let 
      val (opts, files) = 
          GetOpt.getOpt 
          {argOrder = GetOpt.Permute,
           options = options,
           errFn = (fn e => raise Error ("Unsupported option (" ^ e ^ ")"))}
           args
    in
        opts @ map check_readable files
    end

  (* Given a <spec>, give the list of Impl.result -> bool functions that are 
   * expected to pass. *)
  fun get_expected_results spec = 
    let
      fun tokenize str = 
        String.tokens 
            Char.isSpace
            (String.translate 
                 (fn c => 
                     if Char.contains "!,;" c then " " ^ String.str c ^ " " 
                     else String.str c)
                 str)

      val get_fixity =
       fn ";"  => SOME (1, Fixity.LEFT)
        | "=>" => SOME (2, Fixity.RIGHT)
        | "or"  => SOME (3, Fixity.LEFT)
        | ","  => SOME (4, Fixity.LEFT)
        | _ => NONE

      val tree = Fixity.resolve_tree get_fixity (tokenize spec)
                 handle _ => raise Error "Could not parse specification"

      open Fixity (* just to get the T constructor in scope *)

      fun phi tree = 
        case tree of 
          (T (",", trees))      => List.all phi trees
        | (T ("or", trees))     => List.exists phi trees
        | (T ("!", [ tree ]))   => not (phi tree)
        | (T ("lib", []))       => Impl.matches_pred Impl.LIB
        | (T ("typecheck", [])) => Impl.matches_pred Impl.TYPECHECK
        | (T ("gc", []))        => Impl.matches_pred Impl.GC
        | (T ("safe", []))      => Impl.matches_pred Impl.SAFE
        | (T (s, []))           => Impl.name () = s
        | (T (s, _))            => 
          raise Error ("Unexpected arguments to \"" ^ s ^ "\" in predicate")
          
      fun spec tree =
        case tree of
          (T (";", trees)) => List.concat (map spec trees)
        | (T ("=>", [ t_phi, t_spec ])) => 
          if phi t_phi then spec t_spec else []
        | (T ("error", []))               => [ Impl.did_error ]
        | (T ("failure", []))             => [ Impl.did_failure ]
        | (T ("infloop", []))             => [ Impl.did_infloop ]
        | (T ("segfault", []))            => [ Impl.did_segfault ]
        | (T ("abort", []))               => [ Impl.did_abort ]
        | (T ("div-by-zero", []))         => [ Impl.did_div_by_zero ]
        | (T ("return", [ T ("*", []) ])) => [ Impl.did_return NONE ]
        | (T ("return", [ T (num, []) ])) => [ Impl.did_return (SOME (n num)) ]
        | (T (x, _)) => 
          raise Error ("Do not understand specifications involving \""
                       ^ x ^ "\"")
                        
    in spec tree end
            


(*

      val () = if null expected_results then 

    in
      if null expected_results 
      then skipped := !skipped + 1
      else 
        let
          val () = print (pad 11 ("Test " ^ Int.toString (!line) ^ ":") ^
                            str ^ "\n");
          val result = Impl.test files 
        in 
          (result, List.all (fn f => f result) expected_results)
        end
    end
*)

  (* Returns NONE if there's nothing to test.
   * Returns a boolean value representing success or failure and a string 
   *     describing the actual behavior of the test otherwise.
   * Raises Error if the test is poorly-formed. *)
  datatype test_outcome = TEST_SUCCESS | TEST_FAILURE | TEST_TIMEDOUT
  fun test str : (test_outcome * string) option = 
    let 
      val (spec, files) = 
          case String.fields (fn x => x = #"~") str of
            [ spec, files ] => (spec, chk (String.tokens Char.isSpace files))
          | _ => raise Error "Line not of the form <spec> ~ <files>"
      val expected_results = get_expected_results spec
    in 
      if null expected_results then NONE
      else let 
              val result = Impl.test files
              val outcome = 
                  if List.all (fn f => f result) expected_results
                  then TEST_SUCCESS
                  else if Impl.did_infloop result
                  then TEST_TIMEDOUT
                  else TEST_FAILURE
           in SOME (outcome, Impl.result_to_string result) end
    end

  (* Records the result of tests *)
  fun handle_test filename str = 
    if List.all Char.isSpace (String.explode str) then ()
    else let
      val dir = OS.Path.dir filename
      (* val () = print ("Switching to directory of file " ^ filename ^ "\n") *)
      (* val () = print ("Directory is: " ^ dir ^ "\n") *)
      val () = OS.FileSys.chDir dir
      val res =
           (print (pad 11 ("Test " ^ Int.toString (!line) ^ ":") ^ str ^ "\n");
            line := !line + 1;
            test str)
    in
      case res of
         NONE => 
         (skipped := !skipped + 1)
       | SOME (TEST_SUCCESS, _) => 
         (success := !success + 1)
       | SOME (TEST_TIMEDOUT, msg) => 
         (timeout := !timeout + 1; 
          print ("Test timed out unexpectedly: " ^ msg ^ "...\n"))
       | SOME (TEST_FAILURE, msg) => 
         (failure := !failure + 1;
          print ("Test Failed: " ^ #2 (valOf res) ^ "...\n"); 
          failed_tests := (!failed_tests) @
                          [ "In file " ^ filename ^ "\n" ^
                            "Test:   " ^ str ^ "\n" ^ 
                            "Result: " ^ #2 (valOf res) ^ "\n\n" ])
    end handle Error s => 
           (errors := !errors + 1; 
            print ("Error: " ^ s ^ "...\n");
            error_tests := (!error_tests) @
                           [ "In file " ^ filename ^ "\n" ^
                             "Test:   " ^ str ^ "\n\n" ])

  fun process_file filename = 
    let val original_dir = OS.FileSys.getDir () in
    let
      val full_filename = OS.FileSys.fullPath filename
      val {dir, file = filepart} = OS.Path.splitDirFile full_filename
      val file = TextIO.openIn filename
      val contents = 
        case OS.Path.splitBaseExt filepart of
          {ext = SOME "c0", ...} => 
          (base_path := OS.FileSys.getDir ();
           case String.tokens Char.isSpace (valOf (TextIO.inputLine file)) of
             "//test" :: rest =>
             [ String.concatWith " " (rest @ ["~", filename]) ]
           | _ => [])
        | {ext = SOME "test", ...} =>
          (base_path := dir;
           String.tokens  (fn c => c = #"\n") (TextIO.inputAll file))
        | {ext = SOME "c", ...} => []
        | _ => (print ("(Ignoring " ^ filename ^ " - unknown extension)\n");
                [])
    in
      TextIO.closeIn file;
      app (handle_test full_filename) contents;
      OS.FileSys.chDir original_dir    
    end handle OS.SysErr (str, erro) => 
             (* XXX i think this error is wrong: sometimes it fails with
                "No such file or directory" after successfully reading the
                file -- something other than fullPath is raising SysErr? -wjl *)
         (OS.FileSys.chDir original_dir;
          print ("Error reading the file " ^ filename ^ " (" ^ str ^ ")\n\n"))
    end

  fun go args = 
      case args of
        [] => helpful_message ()
      | "-r"::runtime::files => 
        let in
          Impl.set_name runtime;
          go files
        end
      | files =>
        let in
          app process_file files;
          print "\n\nFinal results:\n";
          print ("Successful tests:  " ^ Int.toString (!success) ^ "\n");
          print ("Failed tests:      " ^ Int.toString (!failure) ^ "\n");
          print ("Tests with errors: " ^ Int.toString (!errors) ^ "\n");
          print ("Timeouts: "          ^ Int.toString (!timeout) ^ "\n");
          if (!skipped + !failure + !errors + !success + !timeout) = !line 
          then ()
          else 
            print ("DOESN'T ADD UP: " ^ Int.toString (!skipped) ^ "skipped\n");
          if null (!failed_tests) then ()
          else (print "\n=== Failed test specs: ===\n"; 
                app print (!failed_tests));
          if null (!error_tests) then ()
          else (print "\n=== Tests with errors: ===\n"; 
                app print (!error_tests));
          OS.Process.success
        end
end
