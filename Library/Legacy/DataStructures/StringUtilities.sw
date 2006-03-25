
StringUtilities qualifying spec 
{
  import StringSetSplay

  op freshName  : String * StringSet.Set -> String
  %% Already in String
  %op concatList : List String -> String
  op tokens     : (Char -> Boolean) -> String -> List String

  % freshName (x,names)
  % Generate a fresh name that is not in the list of names given
  % the seed x.

  def freshName (name0, names) = 
    let
      def loop (counter:Nat, name) = 
	if StringSet.member (names, name) then
	  loop(counter + 1, name0 ^ (Nat.toString counter))
	else 
	  name
    in
      loop (0, name0)

  %% def concatList l = List.foldr String.concat "" l

  def tokens break? string = 
    let chars = String.explode string in
    let
      def consChars (chars, strings) = 
        if null chars then
	  strings
	else 
	  cons (String.implode(rev chars), strings)
    in
    let 
      def loop (chars, token_chars, strings) = 
        case chars of
	  | [] -> rev (consChars (token_chars, strings))
	  | ch::chars -> 
	    if break? ch then
	      loop (chars, [], consChars (token_chars, strings))
	    else 
	      loop (chars, cons(ch, token_chars), strings)
    in
      loop (chars, [], [])
}
