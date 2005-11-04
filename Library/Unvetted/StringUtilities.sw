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

    %% Find position of first occurrence of s1 in s2, or None
  op  search : String * String -> Option Nat
  def search (s1, s2) =
    let sz1 = length s1 in
    let sz2 = length s2 in
    let 
      def loop i =
	if i + sz1 > sz2 then 
	  None
	else if testSubseqEqual? (s1, s2, 0, i) then
	  Some i
	else 
	  loop (i + 1)
    in 
      loop 0

  op  testSubseqEqual? : String * String * Nat * Nat -> Boolean
  def testSubseqEqual? (s1, s2, i1, i2) =
    let sz1 = length s1 in
    let 
      def loop i =
	if i1 + i >= sz1 then 
	  true
	else 
	  sub (s1, i1 + i) = sub (s2, i2 + i) 
	  && 
	  loop (i + 1)
    in 
      loop 0

endspec
