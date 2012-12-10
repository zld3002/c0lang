
structure Error = struct

  exception Allocation (* Only raised by native-language implementations *)
  exception Compilation
  exception Uninitialized
  exception Dynamic of string
  exception Internal of string
  exception NullPointer
  exception ArrayOutOfBounds of int * int
  exception ArraySizeNegative of int
  exception AssertionFailed of string
  exception ErrorCalled of string

end
