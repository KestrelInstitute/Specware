XML qualifying spec

  import Parse_Character_Strings

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          GenericTag                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Rules [K4] -- [K10] simplify the parsing (and especially any associated error reporting) for
  %%  several related constructs given by the W3 grammar as:
  %%
  %%  *[23]  XMLDecl       ::=  '<?xml'     VersionInfo  EncodingDecl? SDDecl?   S? '?>' 
  %%  *[77]  TextDecl      ::=  '<?xml'     VersionInfo? EncodingDecl            S? '?>'         
  %%  *[40]  STag          ::=  '<'  Name   (S Attribute)*                       S?  '>' 
  %%  *[42]  ETag          ::=  '</' Name                                        S?  '>'
  %%  *[44]  EmptyElemTag  ::=  '<'  Name   (S Attribute)*                       S? '/>' 
  %%
  %%  plus several supporting rules for the above
  %%
  %% -------------------------------------------------------------------------------------------------
  %% They are all instances of [K4]:
  %%
  %%  [K4]  GenericTag         ::=  GenericPrefix GenericName GenericAttributes GenericPostfix 
  %%  [K5]  GenericPrefix      ::=  Chars - NmToken
  %%  [K6]  GenericName        ::=  NmToken        
  %%  [K7]  GenericAttributes  ::=  List GenericAttribute
  %%  [K8]  GenericAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%  [K9]  GenericPostfix     ::=  Chars - NmToken
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K4]  GenericTag         ::=  GenericPrefix GenericName GenericAttributes GenericPostfix 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Option_GenericTag (start : UChars) : Possible GenericTag =
    case start of
      | 60 (* '<' *) :: tail -> 
         {
	  (prefix,     tail) <- parse_GenericPrefix      tail;
	  (name,       tail) <- parse_GenericName        tail;
	  (attributes, tail) <- parse_GenericAttributes  tail;
	  (whitespace, tail) <- parse_WhiteSpace         tail;
	  (postfix,    tail) <- parse_GenericPostfix     tail;
	  return (Some {prefix     = prefix,
			name       = name,
			attributes = attributes,
			whitespace = whitespace,
			postfix    = postfix},
		  tail)
	  }
      | _ ->
	 return (None, start)

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K5]  GenericPrefix      ::=  Chars - NmToken
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_GenericPrefix (start : UChars) : Required UString =
    %%
    %% This should typically proceed for only a few characters.
    %% It's expecting '' '?' '/'  etc.
    %% but might get nonsense, which will be detected later.
    %% At any rate, don't go more than about 5 characters before 
    %% complaining.
    %%
    %% Return the chars up to, but not including, the close angle,
    %% plus the tail just past that close angle.
    %%
    let
       def probe (tail, n, rev_end_chars) =
	 if n < 1 then
	   error ("Expected namechar soon after <", start, tail)
	 else
	   case tail of
	     | char :: scout ->
	       if name_char? char then
		 return (rev rev_end_chars,
			 tail)
	       else
		 probe (scout, n - 1, cons (char, rev_end_chars))
	     | _ ->
		 error ("EOF looking for namechar after '<'", start, tail)
    in
      probe (start, 5, [])

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K6]  GenericName        ::=  NmToken        
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_GenericName (start : UChars) : Required UString =
    parse_NmToken start

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K7]  GenericAttributes  ::=  List GenericAttribute
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_GenericAttributes (start : UChars) : Required GenericAttributes =
    let 
       def probe (tail, rev_attrs) =
	 {
	  (possible_attribute, scout) <- parse_GenericAttribute tail;
	  case possible_attribute of
	    | None -> 
	      return (rev rev_attrs, 
		      tail)
	    | Some attr ->
	      probe (scout, cons (attr, rev_attrs))
	     }
    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K8]  GenericAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_GenericAttribute (start : UChars) : Possible GenericAttribute =
    {
     (w1,    tail) <- parse_WhiteSpace start;
     case tail of
       | char :: _ ->
	 if name_char? char then
	   {
	    (name,   tail) <- parse_NmToken    tail;
	    (w2,     tail) <- parse_WhiteSpace tail;
	    (eqchar, tail) <- parse_EqualSign  tail;
	    (w3,     tail) <- parse_WhiteSpace tail;
	    (value,  tail) <- parse_QuotedText tail;
	    return (Some {w1     = w1,
			  name    = name,
			  w2      = w2,
			  %%  '='
			  w3      = w3,
			  value   = value},
		    tail)
	   }
	 else
	   return (None, start)
       | _ ->
	   return (None, start)
	  }	   

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K9]  GenericPostfix     ::=  Chars - NmToken
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_GenericPostfix (start : UChars) : Required UString =
    %%
    %% This should typically proceed for only about 0 or 1 characters.
    %% It's expecting '>' '?>' '/>' ']]>' etc.
    %% but might get nonsense, which will be detected later.
    %% At any rate, don't go more than about 5 characters before 
    %% complaining.
    %%
    %% Return the chars up to, but not including, the close angle,
    %% plus the tail just past that close angle.
    %%
    let
       def probe (tail, n, rev_end_chars) =
	 if n < 1 then
	   error ("Expected '>'", start, tail)
	 else
	   case tail of
	     | char :: tail ->
	       if char = 62 (* '>' *) then
		 return (rev rev_end_chars,
			 tail)
	       else
		 probe (tail, n - 1, cons (char, rev_end_chars))
	     | _ ->
	       error ("EOF looking for '>'", start, tail)
    in
      probe (start, 5, [])

endspec


