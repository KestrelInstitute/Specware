
XML qualifying spec

  import Parse_Chars

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Names                                                                               %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [4]  NameChar  ::=  Letter | Digit | '.' | '-' | '_' | ':' | CombiningChar | Extender
  %%  [5]  Name      ::=  (Letter | '_' | ':') (NameChar)*
  %%  [6]  Names     ::=  Name (S Name)*
  %%  [7]  Nmtoken   ::=  (NameChar)+
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %%
  %% -------------------------------------------------------------------------------------------------

  op parse_Name    : UChars -> Required Name
  op parse_NmToken : UChars -> Required NmToken

  def parse_Name (start : UChars) : Required Name =
    case start of
      | first_char :: tail ->
        {
	 (when (~ (latin_alphabetic? first_char))
	  (error ("Expected alphabetic char for name", start, tail)));
	 let def aux (tail, name_chars) =
              case tail of
		| char :: scout ->
		  (if latin_alphanumeric? char then
		     aux (scout, cons (char, name_chars))
		   else
		     return (cons (first_char, rev name_chars), tail))
		| _ ->
		     error ("Eof while parsing name.", start, [])
	 in
	   aux (tail, [])
	   }
      | _ ->
	error ("Eof while parsing name.", start, [])

  def parse_NmToken (start : UChars) : Required Name =
    let def aux (tail, name_chars) =
         case tail of
	   | char :: scout ->
	     (if latin_alphanumeric? char then
		aux (scout, cons (char, name_chars))
	      else
		return (rev name_chars, tail))
	   | _ ->
	     error ("Eof while parsing name.", start, [])
    in
      aux (start, [])

  def latin_alphabetic? char =
    if char < 65(* A *) then
      false
    else if char <= 90(* Z *) then
      true
    else if char < 97(* a *) then
      false
    else 
      char <= 122(* z *) 
      
  def name_char? char = 
    latin_alphanumeric? char

  def latin_alphanumeric? char =
    if char < 65(* A *) then
      false
    else if char <= 90(* Z *) then
      true
    else if char < 97(* a *) then
      false
    else 
      char <= 122(* z *) 

endspec
