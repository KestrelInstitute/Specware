(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import Parse_Character_Strings

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          ElementTag                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Rules [K5] -- [K10] simplify the parsing (and especially any associated error reporting) for
  %%  several related constructs given by the W3 grammar as:
  %%
  %%  *[23]  XMLDecl       ::=  '<?xml'     VersionInfo  EncodingDecl? SDDecl?   S? '?>'
  %%  *[77]  TextDecl      ::=  '<?xml'     VersionInfo? EncodingDecl            S? '?>'
  %%  *[40]  STag          ::=  '<'  Name   (S Attribute)*                       S?  '>'
  %%  *[42]  ETag          ::=  '</' Name                                        S?  '>'
  %%  *[41]  Attribute     ::=  Name Eq AttValue
  %%  *[44]  EmptyElemTag  ::=  '<'  Name   (S Attribute)*                       S? '/>'
  %%
  %%  plus several supporting rules for the above
  %%
  %% -------------------------------------------------------------------------------------------------
  %% They are all instances of [K5]:
  %%
  %%  [K5]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix
  %%  [K6]  ElementTagPrefix   ::=  ( '?' | '/'  | '' )
  %%  [K7]  ElementName        ::=  NmToken
  %%  [K8]  ElementAttributes  ::=  List ElementAttribute
  %%  [K9]  ElementAttribute   ::=  S NmToken S? '=' S? AttValue
  %%                                                             [WFC: No External Entity References]
  %%                                                             [VC:  Attribute Value Type]
  %% [K10]  ElementTagPostfix  ::=  ( '?' | '/'  | '' )
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K5]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix
  %% -------------------------------------------------------------------------------------------------

  def parse_Option_ElementTag (start : UChars) : Possible ElementTag =
    case start of
      | 60 :: tail ->
        %% '<'
        (case tail of 
	   | 33 (* ! *) :: _ -> return (None, start)
	   | _ ->
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
	     })
      | _ ->
	 return (None, start)

  %% -------------------------------------------------------------------------------------------------
  %%  [K6]  ElementTagPrefix   ::=  ( '?' | '/'  | '' )
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementTagPrefix (start : UChars) : Required UString =
    %%
    %% We begin here just after an opening '<'
    case start of
      | 63 (* '?' *) :: tail -> return ([63], tail)
      | 47 (* '/' *) :: tail -> return ([47], tail)
      | _ ->                    return ([],  start)

  %% -------------------------------------------------------------------------------------------------
  %%  [K7]  ElementName        ::=  NmToken
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementName (start : UChars) : Required UString =
    parse_NmToken start

  %% -------------------------------------------------------------------------------------------------
  %%  [K8]  ElementAttributes  ::=  List ElementAttribute
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementAttributes (start : UChars) : Required ElementAttributes =
    let
       def probe (tail, rev_attrs) =
	 {
	  (possible_attribute, scout) <- parse_ElementAttribute tail;
	  case possible_attribute of
	    | None ->
	      return (reverse rev_attrs,
		      tail)
	    | Some attr ->
	      probe (scout, attr::rev_attrs)
	     }
    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%  [K9]  ElementAttribute   ::=  S NmToken S? '=' S? AttValue
  %%                                                             [WFC: No External Entity References]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: No External Entity References]          [K9] *[41] -- no_external_enity_references?
  %%
  %%    Attribute values cannot contain direct or indirect entity references to external entities.
  %%
  %%  Note that "external entity" applies to entity definitions from both the internal and external
  %%  subsets of the DTD.  There are (confusingly) two orthogonal uses of "internal" vs. "external",
  %%  one for internal/external dtd subsets and another for internal/external entities.
  %%
  %%  [Definition: If the entity definition is an EntityValue, the defined entity is called an
  %%   internal entity. ...]
  %%  [Definition: If the entity is not internal, it is an external entity, ...]
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
	    (value,  tail) <- parse_AttValue   tail;
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
  %% [K10]  ElementTagPostfix  ::=  ( '?' | '/'  | '' )
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementTagPostfix (start : UChars) : Required UString =
    case start of
      | 62       (* '>'  *) :: tail -> return ([],   tail)
      | 63 :: 62 (* '?>' *) :: tail -> return ([63], tail)
      | 47 :: 62 (* '/>' *) :: tail -> return ([47], tail)
      | _ ->
        %% TODO: maybe collect junk up to '>'
        hard_error {kind        = EOF,
		    requirement = "An element tag must terminate with '?>' '/>' or '>'.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [(">",  "to terminate start tag <Foo ...> or end tag </Foo ...>"),
				   ("/>", "to terminate empty element tag <Foo .../>"),
				   ("?>", "to terminate xml decl <?xml ... ?>")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}


endspec


