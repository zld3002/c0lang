load "Int";
load "Word";
load "Real";
load "Random";

use "compat-sig.sml";
use "compat-mosml.sml";

use "hashcons-sig.sml";
use "hashcons.sml";
use "nondet.sml";

use "signat.sml";
use "term.sml";
use "termtests.sml";



(* load "bvec";
load "Word";
load "CharVector";


val _ = bdd.init 1000000 10000;

use "nondet.sml";

use "signat.sml";
use "term.sml";
use "termtests.sml";
use "manage.sml";
use "tindex-path.sml";

Manage.init(3,2,20,100000);



fun massivevar 0 = ()
  | massivevar n = 
    let 
	val _ = fdd.extDomain [8] 
    in massivevar (n-1) end *)




(* 
val a = PIndexed.termToSet(TermTest.recurse1 0);
val b = PIndexed.termToSet(TermTest.recurse1 1);
val c = PIndexed.termToSet(TermTest.recurse1 2);
val abc = bdd.OR(bdd.OR(a,b),c);
bdd.fnprintdot "b.dot" b;
bdd.fnprintdot "c.dot" c;
bdd.fnprintdot "abc.dot" (bdd.OR(bdd.OR(a,b),c));
bdd.fnprintdot "x.dot" (PIndexed.termToSet(Term.mkterm("f",2,[Term.Var,Term.mkterm("a",0,[])])));



val [d1] = fdd.extDomain[17];
val [d2] = fdd.extDomain[17];
val [d3] = fdd.extDomain[17];

val x1 = 
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 6),fdd.ithvar d3 1),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 1),fdd.ithvar d3 2),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 16),fdd.ithvar d3 16),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 9),fdd.ithvar d3 11),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 5),fdd.ithvar d3 7),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 2),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 1),fdd.ithvar d3 3),
       bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 11),fdd.ithvar d3 4))))))));


val x2 = 
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 11,fdd.ithvar d2 6),fdd.ithvar d3 3),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 6),fdd.ithvar d3 15),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  6,fdd.ithvar d2 6),fdd.ithvar d3 7),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  1,fdd.ithvar d2 6),fdd.ithvar d3 9),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 13,fdd.ithvar d2 6),fdd.ithvar d3 3),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  7,fdd.ithvar d2 6),fdd.ithvar d3 14),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  4,fdd.ithvar d2 6),fdd.ithvar d3 1),
       bdd.AND(bdd.AND(fdd.ithvar d1  8,fdd.ithvar d2 6),fdd.ithvar d3 8))))))));


val x3 = 
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 11,fdd.ithvar d2 11),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 10,fdd.ithvar d2 4),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  6,fdd.ithvar d2 12),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  1,fdd.ithvar d2 6),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1 13,fdd.ithvar d2 8),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  7,fdd.ithvar d2 9),fdd.ithvar d3 8),
bdd.OR(bdd.AND(bdd.AND(fdd.ithvar d1  4,fdd.ithvar d2 2),fdd.ithvar d3 8),
       bdd.AND(bdd.AND(fdd.ithvar d1  8,fdd.ithvar d2 13),fdd.ithvar d3 8))))))));

bdd.fnprintdot "x1.dot" x1;
bdd.fnprintdot "x2.dot" x2;
bdd.fnprintdot "x3.dot" x3;


val t1 = PIndexed.termToSet (Term.mkterm("f",2,[Term.mkterm("a",0,[]),Term.mkterm("a",0,[])]));
val t2 = PIndexed.termToSet (Term.mkterm("f",2,[Term.mkterm("a",0,[]),Term.mkterm("s",1,[Term.mkterm("z",0,[])])]));
val t3 = PIndexed.termToSet (Term.mkterm("f",2,[Term.mkterm("z",0,[]),Term.mkterm("s",1,[Term.mkterm("a",0,[])])]));
val tset = bdd.OR(t1,bdd.OR(t2,t3));
bdd.fnprintdot "tset.dot" tset;

val clash = Term.mkterm("f",2,[Term.mkterm("a",0,[]),Term.mkterm("a",0,[])]);
val anded1 = bdd.AND(PIndexed.termToSet' (clash,0),tset);
*)
