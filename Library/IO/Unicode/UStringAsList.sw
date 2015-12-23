(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


Unicode qualifying spec

  import UnicodeSig

  type Unicode.UString = List Unicode.UChar

  def Unicode.null? = List.empty?
  def Unicode.all?  = List.forall?
  def Unicode.in?   = List.in?

  def Unicode.ustring (s : String) : UString =
    map uchar (explode s)

  def Unicode.string (ustr : UString) : String =
    %% TODO: handle non-ascii chars!
    implode (map Char.chr ustr)

  def Unicode.^ (x, y) = x ++ y

  def Unicode.nth (ustr : UString, i : Nat) : Option UChar =
    %% list nth attempts to be total, signaling error for out-of-range
    case ustr of
      | char :: tail ->
        if i = 0 then
          Some char
        else
          nth (tail, i - 1)
      | _ -> None 


  % def Unicode.all? pred ustring = foldl (fn (uchar, result) -> result && (pred uchar)) true ustring

  def Unicode.substring? (s1 : UString, s2 : UString) : Bool =
    case (s1, s2) of
      | ([], _) -> true
      | (_, []) -> false
      | (c1 :: t1, c2 :: t2) ->
        let 
	   def matches? (s1, s2) =
	     case (s1, s2) of
	       | ([], _) -> true
	       | (_, []) -> false
	       | (c1 :: t1, c2 :: t2) ->
	         if c1 = c2 then
		   matches? (t1, t2)
		 else
		   false
	in
	  if matches? (t1, t2) then
	    true
	  else
	    substring? (s1, t2)

endspec
