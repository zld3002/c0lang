(* C0 Compiler
 * Symbol tables
 * Author: Kaustuv Chaudhuri <kaustuv@cs.cmu.edu>
 * Updated: Frank Pfenning <fp@cs.cmu.edu>
 *)

(* uses, from $/smlnj-lib/Util/
   structure HashTable
   structure HashString
   functor BinaryMapFn
   functor BinarySetFn
*)

signature SYMBOL =
sig
  type symbol
  val compare : symbol * symbol -> order (* compare symbols by their creation time *)

  val reset : unit -> unit	(* resets the hash table in which the symbols are stored *)
  val symbol : string -> symbol (* returns the symbol with given name (creating if necessary) *)
  val new : string -> symbol (* generates a new symbol with given name *)
  val name : symbol -> string	(* returns a name associated with symbol *)
  val nameFull : symbol -> string	(* returns the full internal name of a symbol *)

  (* symbol tables -- allows association of any type with each symbol *)
  type 'a table
  val empty : 'a table		(* empty table *)
  val digest : (symbol * 'a) list -> 'a table (* prefilled table *)

  val bind : 'a table -> symbol * 'a -> 'a table (* insert new item into table *)
  val look : 'a table -> symbol -> 'a option (* return the value from the table *)
  val look' : 'a table -> symbol -> 'a (* returns value from table, raise Option if not found *)
  val count : 'a table -> int	(* returns the number of items in the table *)

  val elems : 'a table -> 'a list (* return all the data as a list *)
  val elemsi : 'a table -> (symbol * 'a) list (* return the symbols with the associated data *)
  val keys : 'a table -> symbol list (* just the symbols *)

  (* symbol set -- similar to a () Symbol.table, elements can be removed *)
  type set
  val null : set		      (* empty set *)
  val singleton : symbol -> set       (* generate a set with one item *) 
  val add : set -> symbol -> set      (* add a symbol *)
  val remove : set -> symbol -> set   (* remove a symbol *)
  val member : set -> symbol -> bool  (* is the symbol in the set? *)
  val intersection : set * set -> set (* set intersection *)
  val union : set * set -> set	      (* set union *)
  val difference : set * set -> set   (* set difference *)
  val listmems : set -> symbol list   (* list members *)
  val showmems : set -> string (* returns the string of delimited names, for debugging *)
end


structure Symbol :> SYMBOL =
struct
  type symbol = string * int

  fun compare ((n, i), (n', i')) = Int.compare (i, i')

  local
    exception Symbol
    val nexts = ref 0
    fun initht () =
      HashTable.mkTable (HashString.hashString, fn (x, y) => String.compare (x, y) = EQUAL)
      (128, Symbol)
    val ht = ref (initht ())
  in
    fun reset () = (nexts := 0;
		    ht := initht ())
    fun symbol name =
	(case HashTable.find (!ht) name
	  of SOME i => (name, i)
	   | NONE =>
	     let
		 val i = !nexts before nexts := !nexts + 1
	     in
		 HashTable.insert (!ht) (name, i);
		 (name, i)
	     end)
    fun new name = 
       let val i = !nexts before nexts := !nexts + 1
       in (name, i) end
  end

  fun name (n, i) = n
  fun nameFull (n, i) = n ^ "$" ^ (Int.toString i)

  structure Map = BinaryMapFn (struct
				 type ord_key = symbol
				 val compare = compare
			       end)

  type 'a table = 'a Map.map

  val empty = Map.empty
  fun digest l = List.foldr (fn ((s, v), m) => Map.insert (m, s, v)) empty l

  fun bind t (s, x) = Map.insert (t, s, x)
  fun look t s = Map.find (t, s)
  fun look' t s = Option.valOf (look t s)
  fun count t = Map.numItems t
  fun elems t = Map.listItems t
  fun elemsi t = Map.listItemsi t
  fun keys t = Map.listKeys t

  fun delimit' [] s = s
    | delimit' [x] s = s ^ x
    | delimit' (x :: xs) s = delimit' xs (s ^ x ^ ", ")
  fun delimit l = delimit' l "[" ^ "]"

  structure Set = BinarySetFn (struct
				 type ord_key = symbol
				 val compare = compare
			       end)

  type set = Set.set

  val null = Set.empty
  val singleton = Set.singleton
  fun add S s = Set.add (S, s)
  fun remove S s = Set.delete (S, s)
  fun member S s = Set.member (S, s)
  fun intersection (S1, S2) = Set.intersection (S1, S2)
  fun union (S1, S2) = Set.union (S1, S2)
  fun difference (S1, S2) = Set.difference (S1, S2)
  fun listmems S = Set.listItems S
  fun showmems S = delimit (List.map name (Set.listItems S))
end
