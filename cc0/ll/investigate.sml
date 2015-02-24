structure Investigate :> sig

   (* crawl dirname needle
    *
    * looks for submissions within the folder dirname containing
    * the file needle, runs C0 in that directory *)
   val crawl: string -> string -> unit

   (* crawl_print_to_file output_file dirname needle
    *
    * looks for submissions within the folder dirname containing
    * the file needle, runs C0 in that directory
    * puts results in the file output_file *)
   val crawl_print_to_file: string -> string -> string -> unit
end =
struct

fun analyze_program (program: Ast.gdecl list): string =
(* Currently computes cyclomatic complexity for is_in, insert, delete *)
let
  fun count_conds (stmt: Ast.stm) =
      case stmt of
        Ast.Markeds m => count_conds (Mark.data m)
      | Ast.Seq (v, stmts') =>
        List.foldl (fn ((v1, e1), (v2, e2)) => (v1 + v2, e1 + e2))
                   (0, 0) (List.map count_conds stmts')
      | Ast.If (e, s1, s2) =>
        let
          val (v1, e1) = count_conds s1
          val (v2, e2) = count_conds s2
        in
          (v1 + v2 + 1, e1 + e2 + 2)
        end
      | Ast.For t =>
        let
          val (v1, e1) = count_conds (#1 t)
          val (v2, e2) = count_conds (#3 t)
          val (v3, e3) = count_conds (#5 t)
        in
          (v1 + v2 + v3 + 1, e1 + e2 + e3 + 2)
        end
      | Ast.While t =>
        let
          val (v, e) = count_conds (#3 t)
        in
          (v + 1, e + 2)
        end
      | Ast.Return _ => (1, 0)
      | _ => (1, 1)
  fun count (gdecl: Ast.gdecl) = case gdecl of
                      Ast.Function f =>
                      (case (#4 f) of
                         SOME l =>
                         let
                           val (v, e) = (count_conds l)
                         in
                           "," ^ Int.toString (e - v + 2)
                         end
                       | _ => "")
                    | _ => ""
  val result = List.foldl
                   (fn (s1, s2) => s2 ^ s1) ""
                   (List.take (List.drop (List.map count program, 17), 3))

in
  if (String.size result) <= 1
  then ""
  else String.extract (result, 1, NONE)
end

fun pad_zero n = String.implode (List.tabulate (n, fn _ => #"0"))

fun pad_bitvector limit w =
let
   val s = (Word32.fmt StringCvt.BIN o ConcreteState.to_int) w
in
   pad_zero (limit - size s)^s
end

fun investigate_submission output dn needle =
let
   (* Parse out time-of-day information from the directory's name *)
   val dirname = #file (OS.Path.splitDirFile dn)
   val [date, time, rand] = String.tokens (fn x => x = #".") dirname
   val [year, month, day] =
       map (valOf o Int.fromString) (String.tokens (fn x => x = #"-") date)
   val [hour, minute, seconds] =
       map (valOf o Int.fromString) (String.tokens (fn x => x = #":") time)

   (* Read and parse the INFO.txt file *)
   val infofile = OS.Path.joinDirFile {dir = dn, file = "INFO.txt"}
   val info = TextIO.openIn infofile
   val SOME [_, UUID] =
      Option.map (String.tokens Char.isSpace) (TextIO.inputLine info)
   val SOME [_, hostname] =
      Option.map (String.tokens Char.isSpace) (TextIO.inputLine info)
   val SOME (exe :: args) =
      Option.map (String.tokens Char.isSpace) (TextIO.inputLine info)
   val () = TextIO.closeIn info

   (* Run the compiler *)
   (* XXX Rob should modify this so that it still gets the
    * analyze_program function the code even if the code doesn't check *)
   exception FailedAt of string
   val analysis_result = ref "could_not_analyize"
   val compiler_result: string =
   let
      val () = Top.reset ()
      val listlib = OS.Path.joinDirFile {dir = dn, file = "listlib.c0"}
      val sortedlist = OS.Path.joinDirFile {dir = dn, file = needle}
      (* XXX: probably a good idea to add in the test code here? *)
      val sources =
         Top.get_sources_set_flags
           {options = Flags.core_options,
            errfn = (fn _ => raise FailedAt "0,0"),
            versioninfo = "",
            usageinfo = "",
            args = [listlib, sortedlist, "ll/grader.c0"]}
         handle _ => raise FailedAt "0000"
      val {library_headers, program, ...} =
         Top.typecheck_and_load sources
         handle _ => raise FailedAt "1000"
      val () = analysis_result := analyze_program program

      val {...} =
         Top.finalize {library_headers = library_headers}
         handle _ => raise FailedAt "1100"

      fun runcode_1 (f, limit) =
      let in
         ConcreteState.clear_locals Exec.state;
         CodeTab.reload_libs (!Flags.libraries);
         CodeTab.reload (library_headers @ program);
         Builtins.reset {argv = rev (!Flags.runtime_args)};
         "1111"^
         pad_bitvector limit
            (Exec.call (Symbol.symbol f, [], ((0, 0), (0, 0), "_init_")))
      end handle _ => ("1100"^pad_zero limit)

      fun runcode f limit =
         (TimeLimit.timeLimit (Time.fromSeconds 3) runcode_1 (f, limit))
         handle TimeLimit.TimeOut => ("1110"^pad_zero limit)

      val () = OS.FileSys.chDir "bin"
      val result =
         (runcode "is_in_tests" 29)^","^
         (runcode "insert_tests" 13)^","^
         (runcode "delete_tests" 32)
      val () = OS.FileSys.chDir ".."
   in
      result
   end handle FailedAt str =>
              (str^pad_zero 29^","^str^pad_zero 13^","^str^pad_zero 32)

in
   output UUID;
   output ",";
   output needle;
   output ",";
   output (Int.toString day^":"^time);
   output ",";
   output compiler_result;
   output ",";
   output (!analysis_result);
   output "\n";
   ()
end

fun open_submission output dn ds needle =
   case OS.FileSys.readDir ds of
      NONE => OS.FileSys.closeDir ds
    | SOME s =>
      (if s = needle
          then investigate_submission output dn needle
       else ();
       open_submission output dn ds needle)

fun crawl_submissions output dn ds needle n =
   case OS.FileSys.readDir ds of
      NONE => OS.FileSys.closeDir ds
    | SOME s =>
      let val path = OS.Path.joinDirFile {dir = dn, file = s}
      in if OS.FileSys.isDir path
         then open_submission output path (OS.FileSys.openDir path) needle
         else ();
         crawl_submissions output dn ds needle (n+1)
      end

fun crawl dn needle =
   crawl_submissions print dn (OS.FileSys.openDir dn) needle 0

fun crawl_print_to_file filename dn needle =
let
   val file = TextIO.openOut filename
   val output = fn string => TextIO.output (file, string)
in
   crawl_submissions output dn (OS.FileSys.openDir dn) needle 0
   before TextIO.closeOut file
end

end
