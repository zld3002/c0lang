(* entirely-prefix *)

signature TOK = sig

  type tok = string

  datatype direction = LEFT | RIGHT | NONE
  datatype fixity    = PREFIX | POSTFIX | INFIX of direction
  
  val oper : tok -> (int * fixity) option

end

functor Fixity (T : TOK) = struct

  datatype tree = T of T.tok * tree list
  datatype item = Tree of tree | Oper of tok * int * T.fixity | App
  datatype status = Appl | Atom | Oper of int * fixity

  exception Ambiguous
  exception Reduce

  fun next (Tree tree :: [], []) = tree
    | next (stack, [])           = next (reduce stack, [])
    | next (stack, NONE :: toks) = resolve (stack, tok, T.oper tok, toks)   

  and resolve (stack, tok, status, toks) =
    case (stack, status) of
      (stack, NONE) =>                                     (* Atom            *)
      next (Tree (tok, []) :: stack, toks)
    | (stack, SOME (fx, T.PREFIX)) =>                      (* Prefix operator *)
      next (Oper (tok, fx, T.PREFIX) :: stack, toks)
    | (item :: [], SOME (fx, T.INFIX d))                   (* Unopposed nfix  *)
      next (Oper (tok, fx, T.INFIX d) :: item :: [], toks)
    | (item :: Oper (tok1, fx1, f1) :: stack, SOME (fx2, f2)) (* Opposed nfix *)
      if fx1 < fx2 then      (* New oper will be reduced before oper on stack *)
       next (Oper (tok, fx2, f2) :: item :: Oper (tok1, fx1, f1) :: stack, toks)
      else if fx1 > fx2 then (* Time for oper on stack to be reduced          *)
       resolve  
      else (case (f1, f2) of (* Precedence must match                         *)
              (T.INFIX T.LEFT, T.INFIX T.LEFT) => 
              (T.INFIX T.RIGHT, T.INFIX T.RIGHT) => 
            | _ => raise Ambiguous
    
  fun reduce (stack : item list) = 
    case stack of 
      (Tree tr1 :: Oper (tok, _, T.PREFIX)  :: stack) =>
      (Tree (T (tok, [ tr1 ])) :: stack)
    | (Oper (tok, _, T.POSTFIX) :: Tree tr1 :: stack) =>
      (Tree (T (tok, [ tr1 ])) :: stack)
    | (Tree tr1 :: Oper (tok, _, T.LEFT)    :: Tree tr2 :: stack) =>
      (Tree (T (tok, [ tr2, tr1 ])) :: stack)
    | (Tree tr1 :: Oper (tok, _, T.RIGHT)   :: Tree tr2 :: stack) => 
      (Tree (T (tok, [ tr2, tr1 ])) :: stack)
    | (Tree tr1 :: Oper (tok, _, T.NONE)    :: Tree tr2 :: stack) => 
      (Tree (T (tok, [ tr2, tr1 ])) :: stack)
    | (Tree (tok, trs) :: App :: tr2 :: stack) =>
      (Tree (tok, tr2 :: trs) :: stack)
    | _ => raise Reduce

  and next (stack, items) = 
    

  and next (stack : item list, todo : tok list) : tok list= 
    case (stack, todo) of 
      (tree :: [], []) => tree

    (* Reduce prefix *)
    | (stack, (tok, (_, NONE)) :: stack) => 
      resolve (Tr (tok, toks) :: stack, [])
      

    (* This is a case where two non-infix operators are adjacent *)
    | (stack, (tok2, NONE) :: todo) => resolve ([ (tok2]
      let in 
        print ("Die. Stack: " ^ tok1 ^ " Todo: " ^ tok2 ^ "\n");
        raise Domain
      end
    | ()
    |
end

(*

structure Spec = struct

  datatype test (* Tests describe expected outcomes *)
    = Error
    | Infloop 
    | Segfault
    | DivByZero 
    | Return of Word32.word option (* Return NONE means returns anything *)
    | Runs (* This requires only that the code links in shared-library code *)

  datatype desc (* Descriptions describe test suites *)
    = Id of string 
    | Not of desc        (* !desc        *)
    | And of desc * desc (* desc, desc   *)
    | Or of desc * desc  (* desc or desc *)

  datatype spec 
    = Test of test
    | Both of spec * spec
    | Imp of desc * spec

  (* Tokenize *)
  datatype stuff
    = NOT | COMMA | SEMI | OR | IMP | ID of string | RET 
  fun spacer c = 
    if Char.contains "!,;" c then " " ^ String.str c ^ " " else String.str c
  fun tok s = 
    case s of
      "!" => NOT | "," => COMMA | ";" => SEMI | "or" => OR | "=>" => IMP
    | "return" => | RET
  fun tokenize s = 
    map tok String.tokens Char.isSpace (String.translate spacer s)
  
  (* Resolve fixity *)
  fun resolve (xs, NOT, ys) = next (NOT :: xs, ys)
    | resolve (ID s1 :: xs, ID s2, _) = (print ("Die : " ^ s1 ^ " - " ^ s2 ^ "\n"); raise Domain)
    | resolve (xs, ID s, 
   
  and next (ID id :: [], []) = id

end

*)
