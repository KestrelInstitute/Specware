
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
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [4]  NameChar  ::=  Letter | Digit | '.' | '-' | '_' | ':' | CombiningChar | Extender
  %%  [5]  Name      ::=  (Letter | '_' | ':') (NameChar)*
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Name (start : UChars) : Required Name =
    case start of
      | first_char :: tail ->
        {
	 (when (~ (name_start_char? first_char))
	  (error ("Expected alphabetic char for name", start, tail)));
	 let def aux (tail, name_chars) =
              case tail of
		| char :: scout ->
		  (if name_char? char then
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

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [6]  Names     ::=  Name (S Name)*
  %%
  %% -------------------------------------------------------------------------------------------------

  op parse_Names : UChars -> Required Names

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [4]  NameChar  ::=  Letter | Digit | '.' | '-' | '_' | ':' | CombiningChar | Extender
  %%  [7]  Nmtoken   ::=  (NameChar)+
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_NmToken (start : UChars) : Required Name =
    let def aux (tail, name_chars) =
         case tail of
	   | char :: scout ->
	     (if name_char? char then
		aux (scout, cons (char, name_chars))
	      else
		return (rev name_chars, tail))
	   | _ ->
	     error ("Eof while parsing name.", start, [])
    in
      aux (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %%
  %% -------------------------------------------------------------------------------------------------

  op parse_NmTokens : UChars -> Required NmTokens

endspec
