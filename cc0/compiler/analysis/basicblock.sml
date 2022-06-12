   
signature BASICBLOCK =
sig
   type ident = Symbol.symbol
   type tp = Ast.tp
   type stm = Ast.stm
   type vardecl = Ast.vardecl
   datatype basicblock = Block of ident * vardecl list * stm (* block name, args, block body *)

   val createBlock : int * vardecl list * stm -> basicblock

   (* what other interface functions do we need? *)
end

structure BasicBlock :> BASICBLOCK =
struct
   type ident = Symbol.symbol
   type tp = Ast.tp
   type stm = Ast.stm
   type vardecl = Ast.vardecl
   datatype basicblock = Block of ident * vardecl list * stm (* block name, args, block body *)

   (* structure T = SymMap
   type table = basicblock T.map *)
   
   fun createBlock (i, decls, stm) = 
       Block (Symbol.symbol ("BasicBlock#" ^ (Int.toString i)), decls, stm)
   (* val nexts : int ref = ref 0;
   fun reset () = nexts := 0;
   fun next () = let val i = !nexts
                     val () = nexts := i + 1
                 in "BasicBlock#" ^ (Int.toString i) end *)
                 
end
