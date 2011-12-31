structure NativeLibrary :> NATIVELIBRARY = struct

  type library = unit
  type function = unit
  fun load _ = NONE
  fun close _ = ()
  fun get _ _ = NONE

end
