(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


XML qualifying spec

  import Parse_XMLDecl
  import Parse_DTD
  import Parse_Element

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Document entity                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  4.3.2 Well-Formed Parsed Entities:
  %%
  %%  The document entity is well-formed if it matches the production labeled 'document'.
  %%
  %%  [Definition: The document entity serves as the root of the entity tree and a starting-point
  %%   for an XML processor.]
  %%
  %%  This [W3] specification does not specify how the document entity is to be located by an XML
  %%  processor; unlike other entities, the document entity has no name and might well appear on
  %%  a processor input stream without any identification at all.
  %%
  %%  [Definition: XML documents should begin with an XML declaration which specifies the version
  %%   of XML being used.]
  %%
  %%  [Definition: There is exactly one element, called the root, or document element, no part of
  %%   which appears in the content of any other element.]
  %%
  %%  For all other elements, if the start-tag is in the content of another element, the end-tag
  %%  is in the content of the same element. More simply stated, the elements, delimited by start-
  %%  and end-tags, nest properly within each other.
  %%
  %%  [Definition: As a consequence of this, for each non-root element C in the document, there is
  %%   one other element P in the document such that C is in the content of P, but is not in the
  %%   content of any other element that is in the content of P. P is referred to as the parent of C,
  %%   and C as a child of P.]
  %%
  %%  *[1]  document  ::=  prolog element Misc*
  %% *[22]  prolog    ::=  XMLDecl? Misc* (doctypedecl  Misc*)?
  %%
  %%   ==>
  %%
  %%  [K1]  document  ::=  XMLDecl? MiscList doctypedecl? MiscList element MiscList
  %%
  %%                                                             [VC:   Root Element Type]
  %%                                                             [KVC:  Valid DTD]
  %%                                                             [KVC:  Valid Root Element]
  %%                                                             [KVC:  Element Valid]
  %%
  %%  [K2]  MiscList  ::=  Misc*
  %%
  %%  [27]  Misc      ::=  Comment | PI | S
  %%
  %%  [Definition: Markup takes the form of start-tags, end-tags, empty-element tags, entity
  %%   references, character references, comments, CDATA section delimiters, document type
  %%   declarations, processing instructions, XML declarations, text declarations, and any white
  %%   space that is at the top level of the document entity (that is, outside the document
  %%   element and not inside any other markup).]
  %%
  %%  [Definition: All text that is not markup constitutes the character data of the document.]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K1]  document  ::=  XMLDecl? MiscList doctypedecl? MiscList element MiscList
  %% -------------------------------------------------------------------------------------------------

  def parse_Document (start  : UChars) : Required Document =
    {
     (xmldecl,      tail) <- parse_XMLDecl     start;
     (misc1,        tail) <- parse_MiscList    tail;
     (dtd,          tail) <- parse_DTD         tail;
     (misc2,        tail) <- parse_MiscList    tail;
     %% Note that the grammar does not allow the root element to be
     %% obtained via expansion of an entity reference.
     %% Inside the content of elements, however, entity references
     %% may expand into text that includes other elements.
     (root_element, tail) <- parse_Element     (tail, []);
     (misc3,        tail) <- parse_MiscList    tail;
     return ({xmldecl = xmldecl,
	      misc1   = misc1,
	      dtd     = dtd,
	      misc2   = misc2,
	      element = root_element,
	      misc3   = misc3},
	     tail)
     }

  %% -------------------------------------------------------------------------------------------------
  %%  [K2]  MiscList  ::=  Misc*
  %% -------------------------------------------------------------------------------------------------

  def parse_MiscList (start : UChars) : Required MiscList =
    let
       def probe (tail, rev_miscs) =
	 case tail of
	   | [] -> return (reverse rev_miscs, [])
	   | _ ->
	     {
	      (possible_misc, scout) <- parse_Misc tail;
	      case possible_misc of
		| Some misc ->
		  probe (scout, misc::rev_miscs)
		| _ ->
		  return (reverse rev_miscs, tail)
	      }
    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%  [27]  Misc      ::=  Comment | PI | S
  %% -------------------------------------------------------------------------------------------------

  def parse_Misc (start : UChars) : Possible Misc =
    %% Comment | PI | S | doctypedecl | element
    case start of

      %% Comment
      | 60 :: 33 :: 45 :: 45 :: tail ->
        %% '<!--'
        {
	 (comment, tail) <- parse_Comment tail;
	 return (Some (Comment comment),
		 tail)
	}

      %% XML/PI
      | 60 :: 63 :: tail ->
        %% '<?'
        (case tail of

	  %% XML
	  | 120 :: 109 :: 108 :: _ ->
            %% 'xml'
	    {
	     error {kind        = EOF,
		    requirement = "After the initial xmldecl, there should be no other xml decls in an XML Document",
		    start       = start,
		    tail        = tail,
		    peek        = 10,
		    we_expected = [("'<?'",              "PI"),
				   ("'<!--'",            "Comment"),
				   ("#x9 #xA #xD #x20",  "WhiteSpace"),
				   ("'<!DOCTYPE'",       "DTD"),
				   ("'<'",               "Element")],
		    but         = "we saw '<?xml'",
		    so_we       = "pretend its a PI"};
	     (pi, tail) <- parse_PI start;
	     return (Some (PI pi),
		     tail)
	    }

	  %% PI
	  | _ ->
	    {
	     (pi, tail) <- parse_PI start;
	     return (Some (PI pi),
		     tail)
	    })

      %% Whitespace
      | char :: tail ->
	if white_char? char then
	  {
	   (whitespace, tail) <- parse_WhiteSpace start;
	   return (Some (WhiteSpace whitespace),
		   tail)
	   }
	else
	  return (None, start)

      | _ ->
	  hard_error {kind        = EOF,
		      requirement = "Each top-level item in an XML Document should be one of the options below.",
		      start       = start,
		      tail        = [],
		      peek        = 0,
		      we_expected = [("'<?xml'",           "initial xml decl"),
				     ("'<?'",              "PI"),
				     ("'<!--'",            "Comment"),
				     ("#x9 #xA #xD #x20",  "WhiteSpace"),
				     ("'<!DOCTYPE'",       "DTD"),
				     ("'<'",               "Element")],
		      but         = "EOF occurred first",
		      so_we       = "fail immediately"}

endspec
