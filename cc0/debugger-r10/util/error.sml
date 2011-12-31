
structure Error = struct

  exception Dynamic of string
  exception Internal of string
  exception ArrayOutOfBounds of int * int

end
