
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
	  (error (Surprise {context  = "Parsing name",
			    action   = "Pretending character is legal start of name",
			    expected = [("[A-Z][a-z]_:", "Initial character of name")],
			    start    = start,
			    tail     = tail,
			    peek     = 10})));
	 let def aux (tail, name_chars) =
              case tail of
		| char :: scout ->
		  (if name_char? char then
		     aux (scout, cons (char, name_chars))
		   else
		     return (cons (first_char, rev name_chars), tail))
		| _ ->
		  hard_error (EOF {context = "While parsing name.", 
				   start   = start})
	 in
	   aux (tail, [])
	   }
      | _ ->
	hard_error (EOF {context = "While parsing name.", 
			 start   = start})

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
		hard_error (EOF {context = "While parsing NmToken.", 
				 start   = start})
    in
      aux (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %%
  %% -------------------------------------------------------------------------------------------------

  op parse_NmTokens : UChars -> Required NmTokens

endspec
