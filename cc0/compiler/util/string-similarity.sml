(* StringSimilarity: functions about classifying the similarity of strings *)
structure StringSimilarity :> sig 
  (* Simple dynamic programming minimum edit distance 
   * algorithm taken from 15-210 lecture notes.
   * Here, an 'edit' is an insertion or a deletion of any character *)
  val edit_distance : string * string -> int 

  (* did_you_mean: symbol * names -> ()
   * did_you_mean (undeclared, names)
   * suggests items similar to "undeclared" from "names"
   * if any exist *)
  val did_you_mean : Symbol.symbol * Symbol.symbol list -> unit
end = 
struct 
  fun edit_distance (S, T) = 
  let
    val n = String.size S + 1 (* memo table rows *)
    val m = String.size T + 1 (* memo table cols *)

    (* memo[s][t] = loop (i, j) 
     * note we need (|s| + 1) * (|t| + 1)
     * because of the starting indices *)
    val memo: int option array = Array.tabulate (n * m, fn _ => NONE)

    (* loop (i, j) is the memoized version of loop' *)
    fun loop (i, j) = 
    let
      val idx = i * m + j
    in
      case Array.sub (memo, idx) of 
        SOME v => v
      | NONE => 
          let 
            val result = loop' (i, j)
          in 
            result before Array.update (memo, idx, SOME result)
          end 
    end 

    and loop' (i, j) = 
      case (i, j) of 
        (i, 0) => i
      | (0, j) => j
      | (i, j) => 
          if String.sub (S, i - 1) = String.sub (T, j - 1)
            (* Characters are the same, no edit required *)
            then loop (i - 1, j - 1) 
            (* Try either inserting the offending character
             * or deleting it *)
            else 1 + Int.min (loop (i, j - 1), loop (i - 1, j))
  in 
    loop (String.size S, String.size T)
  end 

  fun did_you_mean (g, names) = 
  let
    val num_suggestions = 3
    val similarity_threshold = 5

    (* TODO: extract this logic and re-use it for 
      * variable names and typedef names *)
    val undeclared = Symbol.name g 

    (* Get function names and their similarity *)
    val scores: (string * int) list = 
      let
        fun get_similarity sym = 
            let 
              val name = Symbol.name sym
              val similarity = edit_distance (undeclared, name)
            in
              if similarity <= similarity_threshold
                then SOME (name, similarity)
                else NONE 
            end 
      in 
        List.mapPartial get_similarity names 
      end

    val sorted_scores = 
      ListMergeSort.sort (fn ((_, i), (_, j)) => i > j) scores 

    fun truncate_take 0 _ = []
      | truncate_take _ [] = []
      | truncate_take n (x::xs) = x :: truncate_take (n - 1) xs 

    val best_matches = 
      if List.null sorted_scores 
        then NONE
        else SOME (List.map #1 (truncate_take num_suggestions sorted_scores))
  in 
    Option.app 
      (fn matches => (
        ErrorMsg.info NONE ("perhaps you meant one of:");
        List.app (fn g => print ("              " ^ g ^ "\n")) matches;
        print "\n")
      )
      best_matches
  end
end 