datatype 'a list =
    Nil
  | Data of 'a * 'a list

fun length Nil = 0
  | length (Data (hd,tl)) = 1 + length tl

