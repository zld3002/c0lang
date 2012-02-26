structure NativeFn = 
struct

datatype t = 
   FnPtr of MLton.Pointer.t
 | Native of MLton.Pointer.t -> MLton.Pointer.t

end
