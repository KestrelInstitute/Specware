XML qualifying spec

  import Parse_Character_Strings

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          ElementTag                                                                          %%%
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
  %%  [K4]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix 
  %%  [K5]  ElementTagPrefix   ::=  Chars - NmToken
  %%  [K6]  ElementName        ::=  NmToken        
  %%  [K7]  ElementAttributes  ::=  List ElementAttribute
  %%  [K8]  ElementAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%  [K9]  ElementTagPostfix  ::=  Chars - NmToken
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K4]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Option_ElementTag (start : UChars) : Possible ElementTag =
    case start of
      | 60 (* '<' *) :: tail -> 
         {
	  (prefix,     tail) <- parse_ElementTagPrefix   tail;
	  (name,       tail) <- parse_ElementName        tail;
	  (attributes, tail) <- parse_ElementAttributes  tail;
	  (whitespace, tail) <- parse_WhiteSpace         tail;
	  (postfix,    tail) <- parse_ElementTagPostfix  tail;
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
  %%  [K5]  ElementTagPrefix   ::=  ('?' | '/' | '')
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementTagPrefix (start : UChars) : Required UString =
    %%
    %% We begin here just after an opening '<'
    case start of
      | 63 (* '?' *) :: tail -> return ([63], tail)
      | 47 (* '/' *) :: tail -> return ([47], tail)
      | _ ->                    return ([],   start)

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K6]  ElementName        ::=  NmToken        
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementName (start : UChars) : Required UString =
    parse_NmToken start

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K7]  ElementAttributes  ::=  List ElementAttribute
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementAttributes (start : UChars) : Required ElementAttributes =
    let 
       def probe (tail, rev_attrs) =
	 {
	  (possible_attribute, scout) <- parse_ElementAttribute tail;
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
  %%  [K8]  ElementAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementAttribute (start : UChars) : Possible ElementAttribute =
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
  %%  [K9]  ElementTagPostfix  ::=  ('>' | '?>' | '/>')
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementTagPostfix (start : UChars) : Required UString =
    case start of
      | 62       (* '>'  *) :: tail -> return ([],   tail)
      | 63 :: 62 (* '?>' *) :: tail -> return ([63], tail)
      | 47 :: 62 (* '/>' *) :: tail -> return ([47], tail)
      | _ ->
        %% TODO: maybe collect junk up to '>'
        hard_error (EOF {context = "Parsing tag, looking for '?>' '/>' or '>' to terminate tag",
			 start   = start})


endspec


