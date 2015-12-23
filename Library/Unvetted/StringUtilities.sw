(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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
      if c = #\s then flushW ssw else (ss, show c ^ w)
    in
    project 1 o flushW o foldr addChar ([], "") o explode

  %% Find position of first occurrence after position i of s1 in s2, or None
  op  searchBetween : String * String * Nat * Nat -> Option Nat
  def searchBetween (s1, s2, begp, endp) =
    let sz1 = length s1 in
    let endp = min(length s2,endp) in
    let 
      def loop i =
	if i + sz1 > endp then 
	  None
	else if testSubseqEqual? (s1, s2, 0, i) then
	  Some i
	else 
	  loop (i + 1)
    in 
      loop begp

  %% Find position of first occurrence of s1 in s2, or None
  op  search : String * String -> Option Nat
  def search (s1, s2) =
    searchBetween(s1, s2, 0, length s2)

  op findLastBefore(pat: String, s: String, end_pos: Nat): Option Nat =
    let end_pos = min(end_pos, length s) in
    let len_pat = length pat in
    let def loop(pos, last) =
          case searchBetween(pat, s, pos, end_pos) of
            | Some i -> loop(i+len_pat, Some i)
            | None -> last
    in
    loop(0, None)

  op findLast(pat: String, s: String): Option Nat = findLastBefore(pat, s, length s)

  op skipWhiteSpace(s: String, i: Nat): Nat =
    let len = length s in
    if i >= len then len
      else if whiteSpaceChar?(s @ i)
            then skipWhiteSpace(s, i+1)
            else i

  op findStringBetween(s: String, beg_str: String, end_str: String, start_pos: Nat, fin_pos: Nat): Option String =
    let open_pos = case searchBetween(beg_str,s,start_pos,fin_pos) of
		     | Some n \_rightarrow n
		     | None \_rightarrow fin_pos
    in
    let close_pos = case searchBetween(end_str,s,open_pos+1,fin_pos) of
		     | Some n \_rightarrow n
		     | None \_rightarrow 0
    in
    if close_pos >= fin_pos || close_pos <= open_pos then None
      else Some(subFromTo(s,open_pos, close_pos + 1))

  op  replaceString: String * String * String -> String
  def replaceString(s,pat,rep) =
    case search(pat,s) of
      | None -> s
      | Some i -> subFromTo(s,0,i) ^ rep ^ replaceString(subFromTo(s,i + length pat,length s),pat,rep)

  op  testSubseqEqual? : String * String * Int * Int -> Bool
  %% True if s1 from s1@i1 to end is the same as s2@i2 to s2@(i2+(length s1)-i1)
  def testSubseqEqual? (s1, s2, i1, i2) =
    let sz1 = length s1 in
    if i1 < 0 || i2 < 0 || sz1 - i1 > length s2 - i2 then false
    else
    let 
      def loop i =
	if i1 + i >= sz1 then 
	  true
	else 
	  s1@(i1 + i) = s2@(i2 + i) 
	  && 
	  loop (i + 1)
    in 
      loop 0

  op subseqEqual? (s1: String, s2: String, i1: Int, j1: Int, i2: Int): Bool =
    let sz1 = length s1 in
    if i1 < 0 || j1 < 0 || i2 < 0 || j1 > sz1 || j1 - i1 > length s2 - i2 then false
    else
    let 
      def loop i =
	if i1 + i >= j1 then 
	  true
	else 
	  s1@(i1 + i) = s2@(i2 + i) 
	  && 
	  loop (i + 1)
    in 
      loop 0

  op endsIn?(s: String, pat: String): Bool =
    let len_pat = length pat in
    let len_s   = length   s in
    len_s >= len_pat
      && testSubseqEqual?(pat, s, 0, len_s - len_pat)

  op searchPredFirstAfter (s: String, pred: Char -> Bool, j: Nat): Option Nat =
    let sz = length s in
    let 
      def loop i =
	if i >= sz then 
	  None
	else if pred (s@i) then
	  Some i
	else 
	  loop (i + 1)
    in 
      loop j

 op searchPredLastBefore(s: String, pred: Char -> Bool, j: Nat): Option Nat =
    let 
      def loop i =
	if i = 0 then 
	  None
	else
        let i = i - 1 in
        if pred (s@i) then
	  Some i
	else 
	  loop i
    in 
      loop j

  %% Generalized version of split
  op  splitStringAt: String * String -> List String
  def splitStringAt(s,sep) =
   let len_s = length s in
   let len_sep = length sep in
   let def splitFrom(i,last_match_end) =
        if i + len_sep > len_s
	  then [subFromTo(s,last_match_end,len_s)]
	else if testSubseqEqual? (sep, s, 0, i)
	  then Cons(subFromTo(s,last_match_end,i),
		    splitFrom(i+len_sep,i+len_sep))	  
	else 
	  splitFrom(i + 1,last_match_end)
   in
     splitFrom(0,0)

op splitAtStr(s: String, pat: String): Option(String * String) =
 case search(pat, s) of
   | Some i -> Some(subFromTo(s,0,i),subFromTo(s,i + length pat, length s))
   | None -> None

  op splitStringAtChars(s: String, sep_chars: List Char): List String =
    let def split(i, last_match, result) =
          if i < 0 
            then if last_match = 0 then result
                  else subFromTo(s, 0, last_match) :: result
          else if s@i in? sep_chars
            then split(i - 1, i,
                       show(s@i) :: (if i + 1 = last_match then result
                                       else subFromTo(s, i + 1, last_match) :: result))
            else split(i - 1, last_match, result)
    in
    let len = length s in
    split(len - 1, len, [])

  op  removeEmpty: List String -> List String
  def removeEmpty l =
    filter (fn s -> s ~= "") l

  op  removeWhiteSpace: String -> String
  def removeWhiteSpace s =
    implode (filter (fn c -> ~(whiteSpaceChar? c)) (explode s))

  op  removeInitialWhiteSpace: String -> String
  def removeInitialWhiteSpace s =
    case searchPredFirstAfter(s,fn c -> ~(whiteSpaceChar? c), 0) of
      | Some i -> subFromTo(s,i,length s)
      | None -> s

  op  whiteSpaceChar?: Char -> Bool
  def whiteSpaceChar? c = c in? [#\s,#\t,#\n]

op  stripOuterSpaces(s: String): String =
  let len = length s in
  case searchPredFirstAfter(s,fn c -> ~(whiteSpaceChar? c), 0) of
    | Some firstNonSpace -> 
      (case searchPredLastBefore(s,fn c -> ~(whiteSpaceChar? c), length s) of
        | Some lastNonSpace ->
          subFromTo(s, firstNonSpace, lastNonSpace+1)
        | _ -> s)
    | _ -> s

op capitalize(s: String): String =
  let sz = length s in
  if sz = 0 then s
    else show(toUpperCase(s@0)) ^ map toLowerCase (subFromTo(s, 1, sz))

end-spec
