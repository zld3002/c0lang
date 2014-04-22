(*val SIZE = 200;*)

CM.make "../sources.cm";

val transitive_closure = 
[
  (Syntax.P("path", [Syntax.VAR("x"), Syntax.VAR("y")]),
   [
    Syntax.P("edge",[Syntax.VAR("x"),Syntax.VAR("y")])
   ]),
  (Syntax.P("path", [Syntax.VAR("x"), Syntax.VAR("z")]),
   [
    Syntax.P("edge",[Syntax.VAR("x"),Syntax.VAR("y")]),
    Syntax.P("path",[Syntax.VAR("y"),Syntax.VAR("z")])
   ])
] : Syntax.prog

fun generate_input 0 = []
  | generate_input i = Syntax.P("edge", [Syntax.ICONST(i),Syntax.ICONST(i+1)]) :: (generate_input (i-1))

val output = Syntax.P("path",[Syntax.VAR("x"),Syntax.VAR("y")])

val transit = valOf (McAllester.new transitive_closure);
McAllester.add transit (generate_input SIZE);
McAllester.saturate transit;
val out = McAllester.query transit output;
val sorted = Array.array(SIZE + 1, []) : int list Array.array;
val _ = app (fn Syntax.P("path", [Syntax.ICONST(i),Syntax.ICONST(j)])
		=> Array.update(sorted, i, j :: (Array.sub (sorted, i)))) out

val _ = Array.modify (ListMergeSort.sort op>) sorted

val _ = Array.app (fn L => Utility.say (String.concatWith ", " (map Int.toString L))) sorted

