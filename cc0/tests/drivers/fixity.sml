(* Signature for resolving fixity with (left-associative, highest precedence) 
 * adjacency resolution. *)

signature FIXITY = sig

  datatype fixity = LEFT | RIGHT | NON
  type 'result oper = { prec : int,
                        fixity : fixity,
                        action : 'result * 'result -> 'result}
  datatype ('tok, 'result) input = Atm of 'tok | Op of 'result oper

  exception LeadingInfix
  exception ConsecutiveInfix
  exception PrecConflict 

  (* resolve adj input
   * Basic fixity resolution. 
   * Given a way of dealing with adjacent tokens (adj) and a list of inputs
   * (input), will compute a result or raise one of the above errors. *)
  val resolve : 
      ('tok list -> 'result) 
      -> ('tok, 'result) input list 
      -> 'result

  (* resolve_oper opers adj toks
   * Operation identification + fixity resolution. 
   * Given a function for identifying which tokens are operators (opers), 
   * calls the resolve function appropriately. *)
  val resolve_oper : 
      ('tok -> 'result oper option) 
      -> ('tok list -> 'result) 
      -> 'tok list 
      -> 'result

  (* resolve_tree opers toks 
   * Parses tokens into a specific tree-like structure given the ability
   * to identify which tokens are infix operators. *)
  datatype 'a tree = T of 'a * 'a tree list
  val resolve_tree : ('tok -> (int * fixity) option) -> 'tok list -> 'tok tree

end

structure Fixity :> FIXITY = struct

  datatype fixity = LEFT | RIGHT | NON
  type 'result oper = { prec : int,
                        fixity : fixity,
                        action : 'result * 'result -> 'result}
  datatype ('tok, 'result) input = Atm of 'tok | Op of 'result oper
  datatype 'result item = IsAtm of 'result | IsOp of 'result oper

  exception NoInput
  exception Impossible
  exception LeadingInfix
  exception TrailingInfix
  exception ConsecutiveInfix
  exception PrecConflict 

  (* Collect all the adjacent atoms at the beginning of input *)
  fun gobble_atoms (toks, Atm tok :: input) = gobble_atoms (tok :: toks, input)
    | gobble_atoms (toks, input) = (rev toks, input)

  fun resolve adj input = 
    let

      (* Invariant: the last thing in the list is an IsAtm     *)
      (* Invariant: there is no sequence IsAtm :: IsAtm :: ... *)
      (* Invariant: there is no sequence IsOp  :: IsOp  :: ... *)
      fun go ([], []) = raise NoInput
        | go (IsOp _ :: _, []) = raise TrailingInfix
        | go (IsAtm _ :: IsOp _ :: [], _) = raise Impossible
        | go (IsAtm _ :: IsAtm _ :: _, _) = raise Impossible
        | go (IsAtm _ :: IsOp _ :: IsOp _ :: _, _) = raise Impossible

        | go (IsAtm atm :: [], []) = atm

        (* The end of input is like an operator of super-low precedence. *)
        | go (IsAtm atm2 :: IsOp oper :: IsAtm atm1 :: input, []) =
          go (IsAtm (#action oper (atm1, atm2)) :: input, [])

        (* If there is a leading atom, push a series of atoms. *)
        | go (stack, Atm tok :: input) = 
          let val (toks, input) = gobble_atoms ([ tok ], input) 
          in go (IsAtm (adj toks) :: stack, input) end

        (* If there is a leading operator, analyze the stack! *)
        | go (stack, input as Op oper :: input') =
          let in
            case stack of 
              [] => raise LeadingInfix 
            | (IsOp _  :: _) => raise ConsecutiveInfix 
            | (IsAtm _ :: []) => go (IsOp oper :: stack, input')
            | (IsAtm _ :: IsAtm _ :: _) => raise Impossible
            | (IsAtm _ :: IsOp _  :: []) => raise Impossible
            | (IsAtm _ :: IsOp _  :: IsOp _  :: _) => raise Impossible
            | (IsAtm atm2 :: IsOp oper' :: IsAtm atm1 :: stack') =>
              if #prec oper > #prec oper' (* SHIFT *)
              then go (IsOp oper :: stack, (input'))
              else if #prec oper < #prec oper' (* REDUCE *)
              then go (IsAtm (#action oper' (atm1, atm2)) :: stack', input)
              else (case (#fixity oper, #fixity oper') of
                      (LEFT, LEFT) => (* REDUCE *)
                      go (IsAtm (#action oper' (atm1, atm2)) :: stack', input)
                    | (RIGHT, RIGHT) => (* SHIFT *)
                      go (IsOp oper :: stack, input')
                    | _ => raise PrecConflict)
          end       

    in
      go ([], input)
    end       

  fun resolve_oper opers adj toks =
    let 
      fun mapper tok = 
        case opers tok of 
          NONE => Atm tok
        | SOME oper => Op oper
    in
      resolve adj (map mapper toks)
    end

  datatype 'a tree = T of 'a * 'a tree list
  fun resolve_tree opers toks = 
    let
      fun mapper tok =
        case opers tok of 
          NONE => Atm tok
        | SOME (prec, fixity) => 
          Op {prec = prec, 
              fixity = fixity,
              action = fn (x,y) => T (tok, [ x, y ])}
      fun adj [] = raise Subscript
        | adj (tok :: toks) = T (tok, map (fn x => T (x, [])) toks)
    in
      resolve adj (map mapper toks)
    end

(* 

  and resolve (xs, tokstatus, toks) =
    case (xs, tokstatus) of
      (Tree (tok, trees) :: stack, IsAtom tok') => (* Application             *)
      next (Tree (tok, trees @ [ T (tok', []) ]) :: stack, toks)
    | (stack, IsAtom tok) =>                      (* New atom                 *)
      next (Tree (tok, []) :: stack, toks)
    | (x :: [], IsOp oper) =>                     (* Unopposed operator       *)
      next (Op oper :: x :: [], toks)   
    | (x :: Op (tok', lvl', fs') :: xs, IsOp (tok, lvl, fs)) => (* Opposed    *)
      if lvl > lvl' then                          (* New guy strong           *)
        next (Op (tok, lvl, fs) :: x :: Op (tok', lvl', fs') :: xs, toks)
      else if lvl < lvl' then                     (* New guy weak : reduce    *)
        next (reduce (x :: Op (tok', lvl', fs') :: xs), tok :: toks)
      else (case (fs, fs') of                     (* Guys the same            *)
        (T.LEFT, T.LEFT) =>   
        next (reduce (x :: Op (tok', lvl', fs') :: xs), tok :: toks)
      | (T.RIGHT, T.RIGHT) => 
        next (Op (tok, lvl, fs) :: x :: Op (tok', lvl', fs') :: xs, toks)
      | _ => raise PrecConflict (tok', tok))


          

          go (adj 


resolve (stack, oper tok, toks)

      (* Get all the adjacent tokens, then add the *)
      fun gobble_atms (adj, stack, toks, Atm tok :: input) = 
          gobble_atms (adj, stack, tok :: toks, input)
        | gobble_atms (adj, stack, toks, input) = 
          n
      
      

  datatype tree = T of tok * tree list
  datatype item = Tree of tok * tree list | Op of tok * int * T.fixity
  datatype status = IsRes of tok | IsOp of tok * int * T.fixity

  exception Ambiguous
  exception Reduce

  fun oper tok = 
    case T.oper tok of
      NONE => IsAtom tok
    | SOME (lvl, fx) => IsOp (tok, lvl, fx)

  

  and resolve (xs, tokstatus, toks) =
    case (xs, tokstatus) of
      (Tree (tok, trees) :: stack, IsAtom tok') => (* Application             *)
      next (Tree (tok, trees @ [ T (tok', []) ]) :: stack, toks)
    | (stack, IsAtom tok) =>                      (* New atom                 *)
      next (Tree (tok, []) :: stack, toks)
    | (x :: [], IsOp oper) =>                     (* Unopposed operator       *)
      next (Op oper :: x :: [], toks)   
    | (x :: Op (tok', lvl', fs') :: xs, IsOp (tok, lvl, fs)) => (* Opposed    *)
      if lvl > lvl' then                          (* New guy strong           *)
        next (Op (tok, lvl, fs) :: x :: Op (tok', lvl', fs') :: xs, toks)
      else if lvl < lvl' then                     (* New guy weak : reduce    *)
        next (reduce (x :: Op (tok', lvl', fs') :: xs), tok :: toks)
      else (case (fs, fs') of                     (* Guys the same            *)
        (T.LEFT, T.LEFT) =>   
        next (reduce (x :: Op (tok', lvl', fs') :: xs), tok :: toks)
      | (T.RIGHT, T.RIGHT) => 
        next (Op (tok, lvl, fs) :: x :: Op (tok', lvl', fs') :: xs, toks)
      | _ => raise PrecConflict (tok', tok))

  and reduce xs = 
    case xs of 
      (Tree t1 :: Op (tok, _, _) :: Tree t2 :: stack) => 
      Tree (tok, [ T t2, T t1 ]) :: stack
    | _ => raise Ambiguous

  fun resolvefixity toks = next ([], toks)

*)

end

structure TestFixity = struct

  fun oper "+"  = SOME (4, Fixity.LEFT)
      | oper "*" = SOME (3, Fixity.LEFT)
      | oper "=" = SOME (2, Fixity.NON) 
      | oper "&"  = SOME (1, Fixity.RIGHT) 
      | oper _    = NONE

  val resolve = Fixity.resolve_tree oper o String.tokens Char.isSpace

  fun tree_to_string (Fixity.T (s, [])) = s
    | tree_to_string (Fixity.T (s, ts)) =
      "(" ^ s ^ " " ^ String.concatWith " " (map tree_to_string ts) ^ ")"

  val tests = [("1",             "1"),
               ("1 = 9",         "(= 1 9)"),
               ("1 + 2 + 3",     "(+ (+ 1 2) 3)"), 
               ("1 & 2 & 3",     "(& 1 (& 2 3))"),
               ("1 * 2 + 3",     "(* 1 (+ 2 3))"),
               ("1 + 2 * 3",     "(* (+ 1 2) 3)"),
               ("f x + g y",     "(+ (f x) (g y))"),
               ("f x y + 3",     "(+ (f x y) 3)"),
               ("3 + f x y",     "(+ 3 (f x y))"),
               ("3 + f x y + 9", "(+ (+ 3 (f x y)) 9)"),
               ("3 & f x y & 9", "(& 3 (& (f x y) 9))")]
              
  fun test (str, result) = 
      if (tree_to_string (resolve str)) = result
      then ()
      else print ("ERROR: " ^ str ^ " parsed as\n" ^
                  (tree_to_string (resolve str)) ^ " and not as\n" ^ 
                  result ^ "\n\n")

  fun go () = app test tests

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

  
  (* Resolve fixity *)
  fun resolve (xs, NOT, ys) = next (NOT :: xs, ys)
    | resolve (ID s1 :: xs, ID s2, _) = (print ("Die : " ^ s1 ^ " - " ^ s2 ^ "\n"); raise Domain)
    | resolve (xs, ID s, 
   
  and next (ID id :: [], []) = id

end

*)
