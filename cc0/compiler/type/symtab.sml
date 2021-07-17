(* C0 Compiler
 * Global symbol table, using ../util/symbol.sml
 * The various global tables are listed at the end of this file
 * Frank Pfenning <fp@cs.cmu.edu>
 *)

signature SYMTAB =
sig
    type entry
    val reset : unit -> unit
    val bind : Symbol.symbol * entry -> unit
    val lookup : Symbol.symbol -> entry option
    
    val list : unit -> Symbol.symbol list
    val elemsi : unit -> (Symbol.symbol * entry) list 
end

functor Symtab (type entrytp) :> SYMTAB where type entry = entrytp =
struct
   type entry = entrytp

   val symtab = ref (Symbol.empty : entry Symbol.table)
   fun reset () = ( symtab := Symbol.empty )
   fun bind (id, x) = ( symtab := Symbol.bind (!symtab) (id, x) )
   fun lookup (id) = Symbol.look (!symtab) id
   fun list () = Symbol.keys (!symtab)
   fun elemsi () = Symbol.elemsi (!symtab)
end

signature SYMSET =
sig
    val reset : unit -> unit
    val add : Symbol.symbol -> unit
    val remove : Symbol.symbol -> unit
    val member : Symbol.symbol -> bool
    val list : unit -> Symbol.symbol list
end

functor Symset() :> SYMSET =
struct
    val symset = ref (Symbol.null)
    fun reset () = ( symset := Symbol.null )
    fun add (id) = ( symset := Symbol.add (!symset) id )
    fun remove (id) = ( symset := Symbol.remove (!symset) id handle NotFound => () )
    fun member (id) = ( Symbol.member (!symset) id )
    fun list () = Symbol.listmems (!symset)
end

(* Symtab - global function decls and defns and type defns
 * Used by type checker and code generator *)
structure Symtab = Symtab (type entrytp = Ast.gdecl)

(* Structtab - structure decls and defns *)
structure Structtab = Symtab (type entrytp = Ast.gdecl)

(* Typetab - type definitions, used by lexer *)
structure Typetab = Symtab (type entrytp = Ast.tp * Mark.ext option)

(* Funversiontab - versions of functions with contracts *)
structure Funversiontab = Symtab (type entrytp = Symbol.symbol * int)

(* Libtab - loaded libraries; true means native *)
structure Libtab = Symtab (type entrytp = bool)

(* Filetab - loaded files (with #use "file") *)
structure Filetab = Symtab (type entrytp = unit)

(* UndefUsed - function symbols declared and used, but not yet defined *)
structure UndefUsed = Symset()

(* UndefUnused - function symbols declared, but not yet defined or used *)
structure UndefUnused = Symset()
