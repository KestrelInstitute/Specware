(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec

  import Parse_References         % parse_Reference   [redundant, given Parse_Character_Strings]
  import Parse_ElementTag         % parse_Option_ElementTag
  import Parse_Character_Strings  % parse_Comment, parse_CDSect
  import Parse_PI                 % parse_PI

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Element                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: Each XML document contains one or more elements, the boundaries of which are either
  %%   delimited by start-tags and end-tags, or, for empty elements, by an empty-element tag.
  %%   Each element has a type, identified by name, sometimes called its "generic identifier" (GI),
  %%   and may have a set of attribute specifications.]
  %%
  %%   [39]  element  ::=  EmptyElemTag | STag content ETag
  %%                                                             [WFC: Element Type Match]
  %%                                                             [VC:  Element Valid]
  %%                                                             [KVC: Element Valid]
  %%
  %%  [Definition: The beginning of every non-empty XML element is marked by a start-tag.]
  %%
  %%  The Name in the start- and end-tags gives the element's type.
  %%
  %%  *[40]  STag          ::=  '<' Name (S Attribute)* S? '>'
  %%                                                            *[WFC: Unique Att Spec]
  %%    ==>
  %%  [K32]  STag          ::=  ElementTag
  %%                                                             [KWFC: Start Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%
  %%  [Definition: The Name-AttValue pairs are referred to as the attribute specifications of the
  %%   element],
  %%
  %%  [Definition: with the Name in each pair referred to as the attribute name] and
  %%
  %%  [Definition: the content of the AttValue (the text between the ' or " delimiters) as the
  %%   attribute value.]
  %%
  %%  Note that the order of attribute specifications in a start-tag or empty-element tag is not significant.
  %%
  %%  [Definition: The end of every element that begins with a start-tag must be marked by an
  %%   end-tag containing a name that echoes the element's type as given in the start-tag:]
  %%
  %%  *[42]  ETag          ::=  '</' Name S? '>'
  %%    ==>
  %%  [K33]  ETag          ::=  ElementTag
  %%                                                             [KWFC: End Tag]
  %%
  %%  [Definition: The text between the start-tag and end-tag is called the element's content:]
  %%
  %%  Note: Given the way Kestrel uses the chardata in *[43] for indentation, it makes more sense to
  %%        group it as in [K34].  (See print_Element in XML_Printer.sw)
  %%
  %%  *[43]  content       ::=  CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
  %%    ==>
  %%  [K34]  content       ::=  (CharData? content_item)* CharData?
  %%  [K35]  content_item  ::=  element | Reference | CDSect | PI | Comment
  %%
  %%  [Definition: An element with no content is said to be empty.]
  %%
  %%  The representation of an empty element is either a start-tag immediately followed by an
  %%  end-tag, or an empty-element tag.
  %%
  %%  [Definition: An empty-element tag takes a special form:]
  %%
  %%  *[44]  EmptyElemTag  ::=  '<' Name (S Attribute)* S? '/>' 60]
  %%                                                             [WFC: Unique Att Spec]
  %%    ==>
  %%  [K36]  EmptyElemTag  ::=  ElementTag
  %%                                                             [KWFC: Empty Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [39]  element  ::=  EmptyElemTag | STag content ETag
  %%                                                             [WFC: Element Type Match]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Element Type Match]                     [39]  -- element_types_match?
  %%
  %%    The Name in an element's end-tag must match the element type in the start-tag.
  %% -------------------------------------------------------------------------------------------------

  def parse_Element (start : UChars, pending_open_tags : List (ElementTag)) : Required Element =
    {
     (possible_open_tag, tail) <- parse_OpenTag start;
     case possible_open_tag of
       | Some open_tag ->
         %% open_tag will be one of EmptyElemTag or STag
         (if well_formed_empty_tag? open_tag then
	    return ((Empty open_tag),
		    tail)
	  else
	    {
	     (content, tail) <- parse_Content (tail, open_tag :: pending_open_tags);
	     (etag,    tail) <- parse_ETag    (tail, open_tag :: pending_open_tags);
	     return ((Full {stag    = open_tag,
			    content = content,
			    etag    = etag}),
		     tail)
	    })
       | _ ->
	 hard_error {kind        = WFC,
		requirement = "A document must have a root element.",
		start       = start,
		tail        = tail,
		peek        = 10,
		we_expected = [("<foo ..>",    "Start Tag"),
			       ("<foo .../> ", "Empty Element Tag")],
		but         = "we saw something else instead",
		so_we       = "fail immediately"}
	}

  %% -------------------------------------------------------------------------------------------------
  %%  [K32]  STag          ::=  ElementTag
  %%                                                             [KWFC: Start Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%  [K36]  EmptyElemTag  ::=  ElementTag
  %%                                                             [KWFC: Empty Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Start Tag]                             [K32] *[40] -- well_formed_start_tag?
  %%
  %%    STag  ::=  '<'  Name  (S Attribute)*  S?  '>'
  %%    where Name is not a variant of 'xml'
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Empty Tag]                             [K36] *[44] -- well_formed_empty_tag?
  %%
  %%    EmptyElemTag  ::=  '<'  Name  (S Attribute)*  S?  '/>'
  %%    where Name is not a variant of 'xml'
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Unique Att Spec]                        [K32] [K36] *[40] *[44] -- unique_attributes?
  %%
  %%    No attribute name may appear more than once in the same start-tag or empty-element tag.
  %% -------------------------------------------------------------------------------------------------

  def parse_OpenTag (start : UChars) : Possible ElementTag =
    { (possible_tag, tail) <- parse_Option_ElementTag start;
      case possible_tag of
	| Some tag ->
	  {
	   (when (~ ((well_formed_start_tag? tag) || (well_formed_empty_tag? tag)))
	    (error {kind        = WFC,
		    requirement = "Each element must begin with a start tag or be an empty element tag.",
		    start       = start,
		    tail        = tail,
		    peek        = 10,
		    we_expected = [("<foo ..>",    "Start Tag not starting with 'xml'"),
				   ("<foo .../> ", "Empty Element Tag not starting with 'xml'")],
		    but         = ("an unexpected "
				   ^ (if well_formed_end_tag? tag then "closing" else "unrecognized")
				   ^ " tag: '<"
				   ^ (string tag.name)
				   ^ ">' was seen instead"
                                   ^ (if xml_prefix? tag.name then
					"\n starting with a forbidden prefix 'xml', 'XML', etc."
				      else
					"")),
		    so_we       = "proceed as if that were a start tag"}));
	   return (possible_tag, tail)}
	| _ -> return (None, start)
     }

  %% ----------------------------------------------------------------------------------------------------
  %%  [K33]  ETag          ::=  ElementTag
  %%                                                             [KWFC: End Tag]
  %% ----------------------------------------------------------------------------------------------------
  %%  [KWFC: End Tag]                               [K33] *[42] -- well_formed_end_tag?
  %%
  %%    ETag  ::=  '</'  Name  S?  '>'
  %%    where Name is not a variant of 'xml'
  %% ----------------------------------------------------------------------------------------------------

  def parse_ETag (start : UChars, pending_open_tags : List (STag)) : Required ETag =
    let stag = head pending_open_tags in
    let name = string stag.name     in
    { (possible_tag, tail) <- parse_Option_ElementTag start;
      case possible_tag of
	| Some etag ->
	  {
	   (when (~ (well_formed_end_tag? etag))
	    (error {kind        = Syntax,
		    requirement = "An element must terminate with an end tag.",
		    start       = start,
		    tail        = tail,
		    peek        = 10,
		    we_expected = [("'</" ^ name ^ ">'", "ETag to close earlier STag with that name")],
		    but         = "the tag named " ^ (string etag.name) ^ " seen instead was not an end tag",
		    so_we       = "pretend that tag is an end tag"}));
	   if stag.name = etag.name then
	     return (etag, tail)
	   else
	     {
	      error {kind        = WFC,
		     requirement = "Element Type Match : The Name in an element's end-tag must match the element type in the start-tag.",
		     start       = start,
		     tail        = tail,
		     peek        = 0,
		     we_expected = [("'</" ^ name ^ ">'", "ETag to close earlier STag with that name")],
		     but         = "the unexpected end tag: '</" ^ (string etag.name) ^ ">' was seen instead",
		     so_we       = "pretend an interpolated close tag for " ^ name ^ " was seen"};
	      return ({prefix     = [47],
		       name       = stag.name,
		       attributes = [],
		       whitespace = [],
		       postfix    = []},
		      start)
	     }}
	| _ ->
	  hard_error {kind        = Syntax,
		      requirement = "An element must terminate with an end tag.",
		      start       = start,
		      tail        = tail,
		      peek        = 10,
		      we_expected = [("'</" ^ name ^ ">'", "ETag to close earlier STag with that name")],
		      but         = "the element content terminated without a following end tag",
		      so_we       = "fail immediately"}
	 }

  %% -------------------------------------------------------------------------------------------------
  %%  [K34]  content       ::=  (CharData? content_item)* CharData?
  %% -------------------------------------------------------------------------------------------------

  def entity_value (name) : Env UChars =
    %% this should refer to monad for values of declared entities...
    return (case name of
	      | [97, 112, 111, 115] (* apos *) -> [38]
	      | [108, 116]          (* lt *)   -> [60]
	      | _ -> name)

  def parse_Content (start : UChars, pending_open_tags : List (ElementTag)) : Required Content =
    let
       def parse_items (tail, pending_chars, rev_items) =
	 let (char_data, tail) = parse_XCharData tail in
	 {
	  (possible_item, scout) <- parse_Content_Item (tail, pending_open_tags);
	  case possible_item of
	    | Some item ->
	      (case item of
		 | Reference ref ->
		   (case ref of
		      | Entity {name} -> 
		        { expansion <- entity_value name;
			  parse_items (scout, 
				       pending_chars ++ char_data ++ expansion,
				       rev_items)}
		      | Char cref ->
			parse_items (scout, 
				     pending_chars ++ char_data ++ [cref.char],
				     rev_items))

		 | _ ->
		   parse_items (scout,
				[],
				Cons ((Some (pending_chars ++ char_data), item),
				      rev_items)))
	    | _ ->
	      %% Note:  The valdidator will expand reference items later, which
	      %%         may introduce new sub-eleemnts, etc.
	      %%        The replacement text for each such ref must match the
	      %%         production for "content" (and in fact the replacement
              %%         text might be of type Content) so such such results can
	      %%         essentially be spliced into this content structure,
	      %%         with the mild restriction that any resulting adjacent
	      %%         CharData's are merged, to maintain the Content structure.
	      %%         (Or we could allow Content to have adjacent CharData's.)
	      return ({items   = reverse rev_items,
		       trailer = Some (pending_chars ++ char_data)},
		      tail)
	     }
    in
      parse_items (start, [], [])

  %% -------------------------------------------------------------------------------------------------
  %%  [K35]  content_item  ::=  element | Reference | CDSect | PI | Comment
  %% -------------------------------------------------------------------------------------------------

  def parse_Content_Item (start : UChars, pending_open_tags : List (ElementTag)) : Possible Content_Item =
    %% All the options are readily distinguishable:
    %%
    %% Reference  -- "&" ...
    %% Element    -- "<" Letter ...
    %% PI         -- "<?"
    %% CDSect     -- "<![CDATA[" ...
    %% Comment    -- "<!--"
    %%
    %% So do a little lookahead to avoid needless backtracking...
    %%
    case start of
      | 60 :: tail ->
        %% '<'
        (case tail of
	   | 33 :: 45 :: 45 :: tail ->
	     %% "<!--"
  	     %% parse_Comment assumes we're past "<!--"
	     {
	      (comment, tail) <- parse_Comment tail;
	      return (Some (Comment comment),
		      tail)
	     }
	   | 33 :: 91  :: 67 :: 68 :: 65 :: 84 :: 65 :: 91 :: tail ->
	     %% "<![CDATA["
	     {
	      %% parse_CDSECT assumes we're past "<![CDATA["
	      (cdsect, tail) <- parse_CDSect tail;
	      return (Some (CDSect cdsect),
		      tail)
	     }
	   | 47 :: _ ->
	     %% "</"
	     %% start of an ETag, so not something we're looking for
	     return (None, start)

	   | 63 :: _ ->
	     %% "<?"
	     %% parse_PI assumes we're past '<?'
	     {
	      (pi, tail) <-  parse_PI tail;
	      return (Some (PI pi),
		      tail)
	      }
	   | _ ->
	     {
	      %% parse_Element assumes we're back at the original "<"
	      (element, tail) <- parse_Element (start, pending_open_tags);
	      return (Some (Element element),
		      tail)
	     })

      | 38 :: tail ->
        %% '&'
	{
	 %% parse_Reference assumes we're just past the ampersand.
	 (ref, tail) <- parse_Reference tail;
	 %% Note:  The valdidator will expand reference items such as this later,
	 %%         which may introduce new sub-eleemnts, etc.
         %%        The replacement text for this ref must match the production
         %%         for "content".
	 return (Some (Reference ref),
		 tail)
	}

      | [] ->
	hard_error {kind        = EOF,
		    requirement = "Each item in the element contents must be one of the options below.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("'<!--' ...",      "comment"),
				   ("'<![CDATA[' ...", "unparsed character data"),
				   ("'</' ...",        "end tag"),
				   ("'<?' ...",        "PI"),
				   ("'<' Name ...",    "start tag or empty element tag"),
				   ("'&' ...",         "reference")],
		    but          = "EOF occcurred first",
		    so_we        = "fail immediately"}

      | _ ->
	return (None, start)

endspec