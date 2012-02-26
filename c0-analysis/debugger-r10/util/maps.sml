structure MapI = 
RedBlackMapFn(struct type ord_key = int val compare = Int.compare end)

structure MapS = 
RedBlackMapFn(struct type ord_key = string val compare = String.compare end)

