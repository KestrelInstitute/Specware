
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
	  (error {kind        = Syntax,
		  requirement = "Names must start with letters, underbar, or colon.",
		  start       = start,
		  tail        = tail,
		  peek        = 10,
		  we_expected = [("[A-Z][a-z]", "Letter"),
				 ("[_:]",       "special name char"),
				 ("<see doc>",  "unicode basechar or ideograph")],
		  but         = (describe_char first_char) ^ " is not legal as the first character of a name",
		  so_we       = "pretend '" ^ (string [first_char]) ^ " is the legal start of a name"}));
	 let def aux (tail, name_chars) =
              case tail of
		| char :: scout ->
		  (if name_char? char then
		     aux (scout, cons (char, name_chars))
		   else
		     return (cons (first_char, rev name_chars), tail))
		| _ ->
		  return (cons (first_char, rev name_chars), [])
		      
	 in
	   aux (tail, [])
	   }
      | _ ->
	hard_error {kind        = EOF,
		    requirement = "A name was required.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("[A-Z][a-z]", "Letter"),
				   ("[_:]",       "special name char"),
				   ("<see doc>",  "unicode basechar or ideograph")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}

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
    case start of
      | first_char :: tail ->
        {
	 (when (~ (name_char? first_char))
	  (error {kind        = Syntax,
		  requirement = "The first character of a NmToken is restricted to letters, digits, etc.",
		  start       = start,
		  tail        = tail,
		  peek        = 10,
		  we_expected = [("[A-Z][a-z]", "Letter"),
				 ("[0-9]",      "Digit"),
				 ("[_:-.]",     "special name char"),
				 ("<see doc>",  "unicode basechar or ideograph"),
				 ("<see doc>",  "unicode digit"),
				 ("<see doc>",  "unicode combining char"),
				 ("<see doc>",  "unicode extender  char")],
		  but         = (describe_char first_char) ^ "is not legal as the first character of a NmToken",
		  so_we       = "pretend '" ^ (string [first_char]) ^ "' is the legal start of a NmToken"}));
	 let def aux (tail, name_chars) =
              case tail of
		| char :: scout ->
		  (if name_char? char then
		     aux (scout, cons (char, name_chars))
		   else
		     return (cons (first_char, rev name_chars), tail))
		| _ ->
		  return (cons (first_char, rev name_chars), [])
		      
	 in
	   aux (tail, [])
	   }
      | _ ->
	hard_error {kind        = EOF,
		    requirement = "An NmToken was required.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("[A-Z][a-z]", "Letter"),
				   ("[0-9]",      "Digit"),
				   ("[_:-.]",     "special name char"),
				   ("<see doc>",  "unicode basechar or ideograph"),
				   ("<see doc>",  "unicode digit"),
				   ("<see doc>",  "unicode combining char"),
				   ("<see doc>",  "unicode extender  char")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %%
  %% -------------------------------------------------------------------------------------------------

  op parse_NmTokens : UChars -> Required NmTokens

endspec
