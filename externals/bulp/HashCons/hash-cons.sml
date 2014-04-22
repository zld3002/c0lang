(* hash-cons.sml
 *
 * COPYRIGHT (c) 2001 Bell Labs, Lucent Technologies.
 *
 * Modified 2010 Jakob Max Uecker
 * ja.uecker@jacobs-university.de
 *)

structure HashCons :> HASH_CONS =
  struct

    type 'a obj = {nd : 'a, tag : word, hash : word}

    datatype 'a tbl = Tbl of {
	eq : 'a * 'a -> bool,
	nextTag : word ref,
	tbl : 'a obj list Array.array ref
      }

    val tblSz = PrimeSizes.pick 512

    fun new {eq} = Tbl{
	    eq = eq,
	    nextTag = ref 0w0,
	    tbl = ref(Array.array(tblSz, []))
	  }

    fun clear (Tbl{nextTag, tbl, ...}) = (
	  nextTag := 0w0;
	  Array.modify (fn _ => []) (!tbl))

  (* Cause trouble when used :
   * Sometimes the same object appears with different tags
   * if inserted before and after a grow. Reason unknown.
   * Do not use unless bug found and fixed

    fun grow (Tbl{eq, nextTag, tbl}, nsize) = 
	let
	    val ntbl = Array.array(nsize, [])
	    fun index h = Word.toIntX(Word.mod(h, Word.fromInt nsize))
	    fun copy [] = ()
	      | copy ((obj as {hash, ...})::B) = 
		let
		    val i = index hash
		    val bucket = Array.sub(ntbl, i)
		in
		    Array.update(ntbl, i, obj::bucket)
		end
	in
	    Array.app copy (!tbl) before tbl := ntbl
	end

    fun growIfNeeded (TBL as Tbl{eq, nextTag, tbl}) = 
	let
	    val size = Array.length (!tbl)
	    val nitems = Word.toInt(!nextTag)
	in
	    if nitems >= size
	    then grow (TBL, size + size)
	    else ()
	end
   *)

    fun insert (Table as Tbl{eq, nextTag, tbl}, h, term) = let
	  val tbl' = !tbl
	  val i = Word.toIntX(Word.mod(h, Word.fromInt(Array.length tbl')))
	  val bucket = Array.sub(tbl', i)
	  fun find [] = let
		val id = !nextTag
		val _ = nextTag := (!nextTag + 0wx1)
		val obj = {nd = term, hash = h, tag = id}
		in
		  Array.update(tbl', i, obj::bucket);
		  obj
		end
	    | find ((obj as {nd, hash, ...})::r) =
		if (h = hash) andalso eq(term, nd)
		  then obj
		  else find r
	  in
	    find bucket
	  end

    fun node {nd, tag, hash} = nd
    fun tag  {nd, tag, hash} = tag

    fun same (a : 'a obj, b : 'a obj) = (#tag a = #tag b)
    fun compare (a : 'a obj, b : 'a obj) = Word.compare(#tag a, #tag b)

    fun <+ (a, b) = Word.<<(a, 0w1) + b
    infix <+

    fun cons0 tbl (id, c) = insert (tbl, id, c)

    fun cons1 tbl (id, cf) (b : 'b obj) =
	  insert (tbl, id <+ (#tag b), cf b)

    fun cons2 tbl (id, cf) (b : 'b obj, c : 'c obj) =
	  insert (tbl, id <+ (#tag b) <+ (#tag c), cf(b, c))

    fun cons3 tbl (id, cf) (b : 'b obj, c : 'c obj, d : 'd obj) =
	  insert (tbl, id <+ (#tag b) <+ (#tag c) <+ (#tag d), cf(b, c, d))

    fun cons4 tbl (id, cf) (b : 'b obj, c : 'c obj, d : 'd obj, e : 'e obj) =
	  insert (tbl, id <+ (#tag b) <+ (#tag c) <+ (#tag d) <+ (#tag e),
	    cf(b, c, d, e))

    fun cons5 tbl (id, cf)
	(b : 'b obj, c : 'c obj, d : 'd obj, e : 'e obj, f : 'f obj) =
	  insert (tbl,
	    id <+ (#tag b) <+ (#tag c) <+ (#tag d) <+ (#tag e) <+ (#tag f),
	    cf(b, c, d, e, f))

    fun consList tbl (id, cf) (l : 'b obj list) =
	  insert (tbl, List.foldl (fn ({tag, ...}, sum) => sum <+ tag) id l, cf l)

  (* consing for records *)
    fun consR1 tbl (id, inj, prj) r = cons1 tbl (id, inj) (prj r)
    fun consR2 tbl (id, inj, prj) r = cons2 tbl (id, inj) (prj r)
    fun consR3 tbl (id, inj, prj) r = cons3 tbl (id, inj) (prj r)
    fun consR4 tbl (id, inj, prj) r = cons4 tbl (id, inj) (prj r)
    fun consR5 tbl (id, inj, prj) r = cons5 tbl (id, inj) (prj r)

  end
