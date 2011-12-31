structure Calling :>
sig
  val call: NativeCall.function * Ast.tp * (Ast.tp * ConcreteState.value) list
            -> ConcreteState.value
end = 
struct

structure S = ConcreteState

fun find_ty (ty: Ast.tp): Ast.tp =
   case ty of 
      Ast.TypeName x => (case Symtab.lookup x of
         SOME (Ast.TypeDef (_, ty, _)) => find_ty ty
       | _ => raise Error.Dynamic 
                        ("no definition for type variable " ^ Symbol.name x))
    | Ast.Pointer ty => Ast.Pointer (find_ty ty)
    | Ast.Array ty => Ast.Array (find_ty ty)
    | _ => ty     

fun mapArg (ty, v) = 
   case ty of 
      Ast.Bool => NativeCall.Bool (S.to_bool v)
    | Ast.Int => NativeCall.Int (S.to_int v)
    | Ast.Char => NativeCall.Char (S.to_char v)
    | Ast.Pointer _ =>
      NativeCall.Ptr (S.to_native (#2 (valOf (S.to_pointer v))))
    | Ast.Array _ => NativeCall.Ptr (S.to_native (#2 (S.to_array v)))
    | Ast.String => NativeCall.String (S.to_string v)
    | _ => raise Error.Internal ("Bad argument type " ^ Ast.Print.pp_tp ty)

val array_size = _import "c0_array_length" : MLton.Pointer.t -> int;

fun call (fptr, retty, args) =
   let 
      val args = map (fn (ty, v) => (find_ty ty, v)) args
      val retty = find_ty retty
      val call = (fptr, map mapArg args)
      fun f Ast.Void = (ignore (NativeCall.call_ptr call); S.unit)
        | f Ast.Bool = S.bool (NativeCall.call_bool call)
        | f Ast.Int = S.int (NativeCall.call_int call)
        | f Ast.String = S.string (NativeCall.call_string call)
        | f Ast.Char = S.char (NativeCall.call_char call)
        | f (Ast.Pointer ty) = 
          S.pointer (find_ty ty, S.from_native (NativeCall.call_ptr call))
        | f (Ast.Array ty) = 
          let val p = NativeCall.call_ptr call
          in S.array (find_ty ty, S.from_native p, array_size p) end
        | f _ = 
          raise Error.Internal ("Bad return type " ^ Ast.Print.pp_tp retty)
   in f retty end
   
end
