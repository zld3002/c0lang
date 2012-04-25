
structure Coin :> RUNLINE = 
struct

val help_message =
"Coin - the C0 interpreter.                                                  \n\
\                                                                            \n\
\Being in the Coin interpreter is like being inside of a C0 function. You can\n\
\declare and assign to variables (for instance, by typing `int x = 5;' and   \n\
\then `x++;' or `x /= 2;') and you can see the value of variables and        \n\
\expressions (for instance, by typing `true || false;').                     \n\
\                                                                            \n\
\Remember: every statement or expression must end with a semicolon `;'.      \n\
\                                                                            \n\
\The following special \"pragmas\" allow you to pass commands to Coin.       \n\
\  #functions       - List all available functions                           \n\
\  #help            - Display this message                                   \n\
\  #locals          - Display the contents of all declared local variables   \n\
\  #structs         - List the fields of all available structs               \n\
\  #quit            - Exit the interpreter                                   \n\
\  #reload          - Reload libraries and files; clear local variables      \n\
\                                                                            \n"

structure State = ConcreteState
structure C0 = C0Internal
datatype status = CONTINUE | EXIT of OS.Process.status

fun args (_, _) = CONTINUE

val name = ref "coin"
val args = ref [ "--verbose" ]
val options = Flags.core_options @ Flags.coin_options
val versioninfo = 
 ( "Coin " ^ Version.version
 ^ "(r" ^ BuildId.revision ^ ", " ^ BuildId.date ^ ")")
val errfn = fn msg => (print (msg ^ "\n"); ignore (raise Top.EXIT))

(* Completely resets the interpreter's state; goes so far as to reload files. *)
fun reload () = 
let 
   val usageinfo = 
      GetOpt.usageInfo 
       { header = "Usage: " ^ !name ^ " [OPTONS_AND_SOURCEFILES...]"
       , options = options }

   (* Run the compiler's infrastructure (which calls CommandLine.args) *)
   val () = Top.reset ()
   val sources = 
      Top.get_sources_set_flags
       { options = options
       , errfn = errfn
       , versioninfo = versioninfo
       , usageinfo = usageinfo
       , args = !args}
    val {library_headers, program} = Top.typecheck_and_load sources
    val {library_wrappers} = 
       Top.finalize {library_headers = library_headers}
in 
 ( (* Reset Coin's internal state *)
   State.clear_locals Exec.state

   (* Reload program *)
 ; Flag.guard Flags.flag_verbose
      (fn () => print ("Loading program\n")) ()

   (* Load native (ffi) libraries (invokes the dynamic linker) *)
 ; CodeTab.reload_libs (!Flags.libraries)

   (* Load all C0 code (invokes the pseudocompiler in compile.sml) *)
 ; CodeTab.reload (library_headers @ program))
end


(* Do typechecking, transformation, and execution of a read-in satement *)
fun run stm = 
let 
   val env = State.local_tys Exec.state
   val processed_stm = TypeChecker.typecheck_interpreter env stm
   val annoed_stm = 
      if Flag.isset Flags.flag_dyn_check 
      then DynCheck.contracts_interpreter env processed_stm
      else processed_stm

   (* The modified compiler doesn't give me a real position to put here *)
   val (cmds, labs) = Compile.cStm annoed_stm ((~1,~1),(~1,~1),"<BUG>") 

   (* Make sure that the program doesn't run off the end of the vector *)
   val NOOP = Vector.fromList [ C0.Return NONE ]
   val cmds = Vector.concat [ cmds, NOOP ]

   fun print_codes () = 
   let
      fun print_cmd (i, cmd) =
       ( if (i < 10) then print (Int.toString i ^ ":  ")
         else print (Int.toString i ^ ": ")
       ; print (C0.cmdToString cmd ^ "\n"))
      
      fun print_lab (l, i) =
       ( print ("Label L" ^ Int.toString l)
       ; print (" is cmd " ^ Int.toString i ^ "\n"))
   in 
    ( Vector.appi print_cmd cmds
    ; if (Vector.length labs > 0) then print "----\n" else ()
    ; Vector.appi print_lab labs)
   end
in 
 ( Flag.guard Flags.flag_print_codes print_codes ()
 ; ignore (Exec.exec (cmds, labs)))
end

(* Storing the lex state *)
val remember_lex_state = ref C0Lex.normal
val remember_pos = ref 2
val remember_input: C0Lex.lexresult Stream.front ref = ref Stream.Nil

fun isEOL () = 
  (case !remember_input of 
      Stream.Nil => raise Match
    | Stream.Cons ((Terminal.EOL, _), _) => true
    | _ => false)

fun restart () = 
 ( remember_lex_state := C0Lex.normal
 ; remember_pos := 2
 ; remember_input := Stream.Cons ((Terminal.EOL, (0,0)), fn () => Stream.Nil)
 ; Exec.reset ()
 ; ParseState.reset ()
 ; ParseState.pushfile "<stdio>"
 ; ErrorMsg.reset ())

fun prompt () = 
   if !remember_lex_state = C0Lex.normal andalso isEOL ()
   then (restart (); print "--> ")
   else (print "... ")

fun parse_available_tokens (input, pos, lex_state) =
let
   fun print_value (x, v) =
      print (Symbol.name x ^ " is " ^ State.value_string v ^ "\n")

   fun print_field (Ast.Field (x, ty, _)) = 
      print (" " ^ Ast.Print.pp_tp ty ^ " " ^ Symbol.name x ^ ";")

   fun print_fields flds = 
     (case flds of 
         [] => ()
       | [ fld ] => (print_field fld; print " ")
       | _ => 
          ( print "\n"
          ; app (fn f => (print " "; print_field f; print "\n")) flds))
in case input of 
      Stream.Cons ((Terminal.PRAGMA s, pos), _) => 
        (case String.tokens Char.isSpace s of
            "#quit" :: _ => EXIT (OS.Process.success)
          | "#exit" :: _ => EXIT (OS.Process.success)
          | "#reload" :: _ => (reload (); raise ErrorMsg.Error)
          | "#functions" :: _ => (CodeTab.print (); raise ErrorMsg.Error)
          | "#locals" :: _ => 
             ( app print_value 
                  (map (fn x => (x, State.get_id (Exec.state, x)))
                      (Symbol.keys (State.local_tys Exec.state)))
             ; raise ErrorMsg.Error)
          | "#structs" :: _ => 
            let 
               fun print_struct s =
                 (case s of 
                     (SOME (Ast.Struct (x, SOME flds, _, _))) =>
                       ( print ("struct " ^ Symbol.name x ^ " {")
                       ; print_fields flds
                       ; print "};\n")
                   | _ => raise Error.Internal "Bad struct lookup")
            in
             ( app print_struct 
                  (map Structtab.lookup (Structtab.list ()))
             ; raise ErrorMsg.Error)
            end
          | "#help" :: _ => 
             ( print help_message 
             ; raise ErrorMsg.Error)
          | s :: _ => 
             ( print ("Unrecognized pragma " ^ s ^ "\n")
             ; raise ErrorMsg.Error)
          | _ => raise Error.Internal "Empty pragma")
    | input => 
      let fun analy Stream.Nil = 
                 print ("   Lexer: " ^ C0Lex.toString lex_state ^ "\n")
            | analy (Stream.Cons ((t,_), s)) =
               ( print ("   " ^ Terminal.toString t ^ "\n")
               ; analy (s ()))
      in case Parse.parse_stm input of
            NONE => 
             ( () (* print "ANALYSIS\n"; analy input *)
             ; remember_pos := pos
             ; remember_lex_state := lex_state
             ; remember_input := input
             ; CONTINUE (* Get more input! *))
          | SOME (stm, remaining_input) => 
             ( run stm
             ; parse_available_tokens (remaining_input, pos, lex_state))
      end
end handle ErrorMsg.Error => (restart (); CONTINUE) 

fun appendeol str str' = 
   case str of 
      Stream.Nil => raise Match
    | Stream.Cons ((Terminal.EOL, _), _) => str' ()
    | Stream.Cons (t, str) => Stream.Cons (t, fn () => appendeol (str ()) str')

fun runline s =
let
   val (tokstream, pos, lex_state) = 
      C0Lex.lineLexer
       ( Stream.fromList (explode s)
       , !remember_pos
       , !remember_lex_state)
in
   if !ErrorMsg.anyErrors then (restart (); CONTINUE)
   else parse_available_tokens 
           (appendeol (!remember_input) tokstream, pos, lex_state)
end

fun start (initial_name, initial_args) = 
let 
   (* Raise the correct flag if the compiler died *)
   (* XXX: this won't work if it's actually the parsing of args that breaks *)
   fun compilerDied () = Posix.Process.exit 0wx2 
in
 ( name := initial_name
 ; args := initial_args
 ; reload ()
 ; print (versioninfo ^ "\n")
 ; print ("Type `#help' for help or `#quit' to exit.\n")
 ; NONE)
handle Top.EXIT => 
        ( Flag.guard Flags.flag_exec compilerDied ()
        ; SOME OS.Process.failure)
     | ErrorMsg.Error => 
        ( print "Unable to load files, exiting...\n"
        ; Flag.guard Flags.flag_exec compilerDied ()
        ; SOME OS.Process.failure)
end
end

structure Server = 
   Server (structure Runline = Coin
           structure SigINT = SigINT) 