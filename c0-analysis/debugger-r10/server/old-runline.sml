(* Runline implementation *)
(* Rob Simmons *)

structure Runline (* :> RUNLINE *) = struct

 open Global

 structure ST = SimpleTok		    
 structure P = Parsing
 structure S = Stream

 fun start(_,_) = print ("XDLog "^versionstring^"\n")

 datatype cmd = 
	  TOK of string
	| INT of int
	| STR of string

 val commandparser = ST.default TOK INT STR


 (* STATE AND DATA *)

 val sig_state : Signat.state option ref = ref NONE

	
 val help =
  "quit \n"^
  "     exit the server\n"^
  "load sig \"[filename]\"\n"^
  "     clear state, load the signature/idb [filename]\n"^
  "load edb \"[filename]\"\n"^
  "     load extensional database [filename]\n"^
  "clear {edb,sig}\n"^
  "     clear the extensional database, or the EDB and the signature\n"^
  "print {types,constants,rules,sig,flat}\n"^
  "     print the desired information\n"^
  "bddbddb \"[base_filename]\"\n"^
  "     Ouput flattened information for BDDBDDB. \n"^
  "     bddbddb \"mydir/program\" \n"^
  "     would put the main file at mydir/program.datalog and all other\n"^
  "     files in a new directory mydir/program/\n"^
  "help - print this message\n"





 (* INITIALIZATION AND LOADING *)

 fun safe_openOut filename = 
     TextIO.openOut filename
     handle IO.Io({cause,...}) => 
	    raise Error("Could not open file: "^exnMessage cause)

 fun safe_mkDir dirname = 
     OS.FileSys.mkDir dirname
     handle (exn as OS.SysErr(message,num)) => 
	    if OS.FileSys.isDir(dirname) then ()
	    else raise Error("Could not create directory: "^message)

 fun init (INT(n) :: _) = (HashTerm.init n; OK)
   | init _ = raise Error("Bad arguments to 'init' command")

 fun clear(TOK("edb")::_) = 
     (edb := []; 
      HashTerm.init defaultHashTerm;
      (* Reset Signat to state post-sig (possibly removing constants) *)
      case !sig_state of NONE => Signat.reset() | SOME(s) => Signat.set(s);
      OK)
   | clear(TOK("sig")::_) = 
     (edb := []; 
      HashTerm.init defaultHashTerm;
      Signat.reset();
      sig_state := NONE;
      OK) 
   | clear(_) = raise Error("Bad arguments to 'clear' command")


 fun load_sig (STR(filename) :: _) = 
    let
	val () = Signat.reset()
	val () = edb := []
	val () = HashTerm.init defaultHashTerm
	val s = Parser.sigstream(filename, Parser.filestream filename)
	    handle IO.Io({cause,...}) => 
			    raise Error("Could not open file: "^
					exnMessage cause)
	fun loop(stream) = 
	    case S.force stream of
		S.Cons((NONE,_),_) => ()
	      | S.Cons((SOME d,pos),stream) => 
		let
		    val recon = Recon.reconsig d
			handle Error(s) =>
			       raise Error(s^" "^"\nLocation: "^
					   Pos.toString pos)
		   (* val () = print (Print.sigdecl recon^"\n") *)
		    val () = Signat.install recon
			handle Signat.Duplicate(s) =>
			       raise Error("Duplicate definition '"^s^"' at "^
					   Pos.toString pos)
		in
		    loop stream
		end
	      | S.Nil => raise Error("Parsing ended abnormally") 
    in
	Signat.reset(); 
	loop s; 
	sig_state := SOME(Signat.checkpoint()); 
	OK
    end
   | load_sig _ = raise Error("Bad arguments to 'load sig' command")



 fun load_edb (STR(filename) :: _) = 
     let 
	 val s = Parser.edbstream(filename,Parser.filestream filename)
	     handle IO.Io({cause,...}) => 
		    raise Error("Could not open file: "^
				exnMessage cause)

	 val facts = ref []

	 fun install(IntSyn.Decl(cdecl),pos)   = 
	     (let val _ = Signat.installc cdecl in () end
       	      handle Signat.Duplicate(s) =>
		     raise Error("Duplicate definition '"^s^"' at "^
				 Pos.toString pos))

	   | install(IntSyn.Fact(tm as IntSyn.Term(cid,tms),tid),_) = 
	     (case tid of 
		  0 => facts := (cid,map HashTerm.get_rep tms) :: !facts
		| n => (HashTerm.get_rep tm; ()))
	     
	   | install(IntSyn.Fact(_,_),_) = raise Match
					     
	 fun loop(stream) = 
	     case S.force stream of 
		 S.Cons((NONE,_),_) => ()
	       | S.Cons((SOME d,pos),stream) => 
		 let 
		     val recon = Recon.reconedb d
			 handle Error(s) => raise Error(s^" "^"\nLocation: "^
							Pos.toString pos)
		     val () = install(recon,pos)
		 in
		     loop stream
		 end
	       | S.Nil => raise Error("Parsing ended abnormally")

     in
	 loop(s);
	 edb := !edb @ rev(!facts);
	 OK
     end 
   | load_edb _ = raise Error("Bad arguments to 'load edb' command")




 (* PRINTING *)

 fun printT()= Signat.appT(fn x => print (Print.sigdecl(IntSyn.TDecl(x))^"\n"))
 fun printC()= Signat.appC(fn x => print (Print.sigdecl(IntSyn.CDecl(x))^"\n"))
 fun printR()= Signat.appR(fn x => print (Print.sigdecl(IntSyn.RDecl(x))^"\n"))

 fun printflatT() = 
     Signat.appR
	 (fn x => print (Flatten.toString(Flatten.flatten x)^"\n"))


 fun print' (TOK("types")     :: _) = (printT(); OK)
   | print' (TOK("constants") :: _) = (printC(); OK)
   | print' (TOK("rules")     :: _) = (printR(); OK)
   | print' (TOK("sig") :: _) =
     (print "# Types\n"; printT();
      print "\n# Constants\n"; printC();
      print "\n# Rules\n"; printR();
      OK)
   | print' (TOK("flat")      :: _) = (printflatT(); OK)
   | print' _ = raise (Error "Bad argument to 'print' command")




 (* OUTPUT TO BDDBDDB *)

 fun write_term_edb filename htable = 
     let
	 val table = HashTerm.get_table()

	 val out = safe_openOut filename
	 fun act rep = 
	     let 
		 val find = HashTable.lookup htable
		 val HashCons.Spine(cid,repl) = HashCons.exposeM table rep
		 val num = Int.toString (find rep)
		 val numl = map Int.toString (map find repl)
		 val title = "fun_"^Signat.cidToString cid
		 val body = concat(map (fn s => s^",") numl)
		 val str = title^"("^body^num^").\n"
	     in 
		 TextIO.output(out,str)
	     end
     in
	 HashCons.appM act table;
	 TextIO.closeOut out
     end 

 fun write_fact_edb filename htable = 
     let 
	 val out = safe_openOut filename

	 fun toStr [] = ""
	   | toStr [s] = s
	   | toStr (s::sl) = s^","^toStr sl

	 fun act (cid,reps) = 
	     let
		 val find = HashTable.lookup htable
		 val numl = map Int.toString (map find reps)
		 val title = Signat.cidToString cid
		 val body = toStr numl
	     in
		 TextIO.output(out,title^"("^body^").\n")
	     end
     in
	 List.app act (!edb);
	 TextIO.closeOut out
     end

 fun bddbddb(STR(file_base) :: _) = 
     let
	 val file_program = file_base^".datalog"
	 val dir_base = file_base^"/"
	 val dir_relative = OS.Path.file file_base
	 val file_domains = dir_base^"domains"
	 val file_facts   = dir_base^"fact.edb"
	 val file_terms   = dir_base^"term.edb"

	 val out = safe_openOut file_program
	 val ()  = safe_mkDir dir_base
	 val (map,htable) = HashTerm.get_map(dir_base)

	 fun dodomains() =
	     let
		 val out = safe_openOut file_domains 
		 fun mapper(0,_) = () 
                   | mapper(tid,name) = 
		     TextIO.output(out, 
				   name^" "^
				   Int.toString(Vector.sub(map,tid))^" "^
				   name^".map\n");
	     in
		 Signat.appiT mapper;
		 TextIO.closeOut out
	     end

	 fun dotyp [] = ""
	   | dotyp [0] = ""
	   | dotyp [tid] = 
	     let
		 val tp = Signat.tidToString tid
	     in
		 tp^":"^tp^"0"
	     end
	   | dotyp[tid,0] = dotyp[tid]
	   | dotyp(tid::tids) = 
	     let 
		 val tp = Signat.tidToString tid
	     in
		 tp^":"^tp^"0, "^dotyp tids
	     end
     in
	 (* Write auxillary information to directory *)
	 dodomains();
	 write_fact_edb file_facts htable;
	 write_term_edb file_terms htable;

	 (* Header information *)
	 TextIO.output(out,"# Ouput from bidden "^versionstring^"\n\n");
	 TextIO.output(out,".basedir \""^dir_relative^"\"\n");
	 TextIO.output(out,".include \"domains\"\n");

	 (* Types *)
	 TextIO.output(out,"\n# Relations\n");
	 Signat.appiC
	     (fn (cid,(name,tids)) => 
	     	 if Signat.cidToBaseType(cid) = 0 
		 then TextIO.output(out,name^"("^dotyp tids^")\n")
		 else TextIO.output(out,"fun_"^name^"("^dotyp tids^")\n"));

	 (* Output rules *)
	 TextIO.output(out,"\n# Rules\n");
	 Signat.appR
	     (fn x => 
		 TextIO.output
		     (out, Flatten.toString(Flatten.flatten x)^"\n"));
	 
	 (* Include EDB in file *)
	 TextIO.output(out,"\n# Include edb\n");
	 TextIO.output(out,".include fact.edb\n");
	 TextIO.output(out,".include term.edb\n");
	 TextIO.closeOut(out);
	 OK
     end 
   | bddbddb _ = raise (Error "Bad argument to 'bddbddb' command")
 
  
 fun runline s = 
     case ST.tokenize commandparser (ST.stringstream s) of
	 TOK("stats") :: _ => 
	 let
	     fun eff n = (print (Int.toString n) ; print ",");
	     val hist = HashTerm.gethistogram ();
	 in
	     print "Hash table utilization:\n"; 
	     Vector.app eff hist; print "\n";
	     OK
	 end

       | TOK("quit")                 :: ts => EXIT(OS.Process.success)
       | TOK("init")                 :: ts => init ts
       | TOK("load") :: TOK("sig")   :: ts => load_sig ts
       | TOK("load") :: TOK("edb")   :: ts => load_edb ts
       | TOK("clear")                :: ts => clear ts
       | TOK("print")                :: ts => print' ts
       | TOK("bddbddb")              :: ts => bddbddb ts
       | TOK("help")                 :: ts => (print help; OK)
       | _ => raise (Error "Unrecognized command, type 'help' for help")


end

