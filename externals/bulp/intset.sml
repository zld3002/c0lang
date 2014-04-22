
structure IntSet = BinarySetFn 
		   (struct 
		    type ord_key = int
		    val compare = Int.compare
		    end
		   )
