(*
2005:03:17
LM

*)

String qualifying spec

  type NonEmptyString = (String | posNat? o length)

  % split on spaces; elements of result are space-free
  % For example, split " Hello  World  " = ["Hello", "World"]
  op  split : String -> List NonEmptyString
  def split =
    let def flushW (ssw as (ss: List NonEmptyString, w : String)) =
      if posNat?(length w) then (Cons(w, ss), "")
      else ssw
    in
    let def addChar(c : Char, ssw as (ss: List NonEmptyString, w : String)) =
      if c = #\s then flushW ssw else (ss, toString c ^ w)
    in
    project 1 o flushW o foldr addChar ([], "") o explode

endspec
