
XML qualifying spec

  import Parse_References         % parse_Reference   [redundant, given Parse_Character_Strings]
  import Parse_ElementTag         % parse_Option_ElementTag
  import Parse_Character_Strings  % parse_Comment, parse_CDSect
  import Parse_PI                 % parse_PI

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Element                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %%  [39]  element  ::=  EmptyElemTag | STag content ETag 
  %%
  %%                                                             [WFC: Element Type Match] 
  %%                                                             [VC:  Element Valid]
  %%
  %% *[40]  STag          ::=  '<' Name (S Attribute)* S? '>' 
  %%
  %%                                                             [WFC: Unique Att Spec]
  %%   ==>
  %% [K25]  STag          ::=  ElementTag                            
  %%
  %%                                                             [KC:  Proper Start Tag]
  %%                                                             [WFC: Unique Att Spec]
  %% 
  %% *[41]  Attribute     ::=  Name Eq AttValue 
  %%   ==>
  %%  [K8]  ElementAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%
  %%                                                             [VC:  Attribute Value Type]
  %%                                                             [WFC: No External Entity References]
  %%                                                             [WFC: No < in Attribute Values]
  %%
  %% *[42]  ETag          ::=  '</' Name S? '>'
  %%   ==>
  %% [K26]  ETag          ::=  ElementTag                   
  %%
  %%                                                             [KC:  Proper End Tag]
  %%
  %%  Since the chardata in [43] is typically used for indentation, 
  %%  it makes more sense to group it as in [K18]:
  %%
  %% *[43]  content       ::=  CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
  %%   ==>
  %% [K27]  content       ::=  content_item* CharData?
  %% [K28]  content_item  ::=  CharData? (element | Reference | CDSect | PI | Comment
  %% 
  %% *[44]  EmptyElemTag  ::=  '<' Name (S Attribute)* S? '/>' 60]
  %%
  %%                                                             [WFC: Unique Att Spec]
  %%   ==>
  %% [K29]  EmptyElemTag  ::=  ElementTag
  %%
  %%                                                             [KC:  Proper Empty Tag]
  %%                                                             [WFC: Unique Att Spec]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [39]  element  ::=  EmptyElemTag | STag content ETag 
  %%
  %%                                                             [WFC: Element Type Match] 
  %%                                                             [VC:  Element Valid]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Element (start : UChars, pending_open_tags : List (ElementTag)) : Possible Element =
    {
     (possible_open_tag, tail) <- parse_OpenTag start;
     case possible_open_tag of
       | Some open_tag ->
         %% open_tag will be one of EmptyElemTag or STag
         (if empty_tag? open_tag then
	    return (Some (Empty open_tag), 
		    tail)
	  else
	    {
	     (content, tail) <- parse_Content (tail, cons (open_tag, pending_open_tags));
	     (etag,    tail) <- parse_ETag    (tail, cons (open_tag, pending_open_tags));
	     return (Some (Full {stag    = open_tag, 
				 content = content, 
				 etag    = etag}),
		     tail)
	    })
       | _ ->
	 return (None, start)
	}

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K25]  STag          ::=  ElementTag                            
  %%
  %%                                                             [KC:  Proper Start Tag]
  %%                                                             [WFC: Unique Att Spec]
  %%
  %% [K29]  EmptyElemTag  ::=  ElementTag
  %%
  %%                                                             [KC:  Proper Empty Tag]
  %%                                                             [WFC: Unique Att Spec]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_OpenTag (start : UChars) : Possible ElementTag =
    { (possible_tag, tail) <- parse_Option_ElementTag start;
      case possible_tag of
	| Some tag ->
	  {
	   (when (~ ((start_tag? tag) or (empty_tag? tag)))
	    (error {kind        = WFC,
		    requirement = "Each element must begin with a start tag or be an empty element tag",
		    problem     = ("Unexpected "
				   ^ (if end_tag? tag then "closing" else "unrecognized") 
				   ^ " tag: '</" 
				   ^ (string tag.name)
				   ^ ">'"),
		    expected    = [(" ", "Start Tag"),
				   (" ", "Empty Element Tag")],
		    start       = start,
		    tail        = tail,
		    peek        = 10,
		    action      = "Proceed as if it were a start tag"}));
	   return (possible_tag, tail)}
	| _ -> return (None, start)
     }

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K27]  content       ::=  content_item* CharData?
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Content (start : UChars, pending_open_tags : List (ElementTag)) : Required Content =
    let 
       def parse_items (tail, rev_items) =
	 let (char_data, tail) = parse_CharData tail in
	 {
	  (possible_item, scout) <- parse_Content_Item (tail, pending_open_tags);
	  case possible_item of
	    | Some item ->
	      parse_items (scout,
			   cons ((char_data, item),
				 rev_items))
	    | _ -> 
	      return ({items   = rev rev_items, 
		       trailer = char_data},
		      tail)
	     }
    in
      parse_items (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K28]  content_item  ::=  CharData? (element | Reference | CDSect | PI | Comment
  %%
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
      | 60 (* '<' *) :: tail ->
        (case tail of
	   | 33 :: 45 :: 45 (* '!--' *) :: tail -> 
 	     %% "<!--"
	     {
	      %% parse_Comment assumes we're past "<!--"
	      (comment, tail) <- parse_Comment tail; 
	      return (Some (Comment comment),
		      tail)
	     }
	   | 33 :: 91  :: 67 :: 68 :: 65 :: 84 :: 65 :: 91 (* '![CDATA[' *) :: tail ->
	     %% "<![CDATA["
	     {
	      %% parse_CDSECT assumes we're past "<![CDATA["
	      (cdsect, tail) <- parse_CDSect tail;   
	      return (Some (CDSect cdsect),
		      tail)
	     }
	   | 47 (* '/' *) :: _ -> 
	     %% "</"
	     %% start of an ETag, so not something we're looking for
	     return (None, start)
	   | 63 (* '?' *) :: _ -> 
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
	      (possible_element, tail) <- parse_Element (start, pending_open_tags); 
	      case possible_element of
		| Some element ->
		  return (Some (Element element),
			  tail)
		| _ ->
		  return (None, start)
	      })
      | [] ->
	hard_error {kind        = EOF,
		    requirement = "Each item in the element contents must be one of the options below.",
		    problem     = "EOF occcurred first.",
		    expected    = [("'<!--' ...",      "comment"),
				   ("'<![CDATA[' ...", "unparsed character data"),				   
				   ("'</' ...",        "end tag"),				   
				   ("'<?' ...",        "PI"),
				   ("'<' Name ...",    "start tag or empty element tag"),				   
				   ("'&' ...",         "reference")],
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    action      = "immediate failure"}
      | 38  (* '&' *)   :: tail -> 
	{
	 %% parse_Reference assumes we're just past the ampersand.
	 (ref, tail) <- parse_Reference start;
	 return (Some (Reference ref),
		 tail)
	}
      | _ ->
	return (None, start)


  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K26]  ETag          ::=  ElementTag                   
  %%
  %%                                                             [KC:  Proper End Tag]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ETag (start : UChars, pending_open_tags : List (STag)) : Required ETag =
    let stag = hd pending_open_tags in
    let name = string stag.name     in
    { (possible_tag, tail) <- parse_Option_ElementTag start;
      case possible_tag of
	| Some etag ->
	  {
	   (when (~ (end_tag? etag))
	    (error {kind        = Syntax,
		    requirement = "An element must terminate with an end tag",
		    problem     = "tag named " ^ (string etag.name) ^  " was not an end tag",
		    expected    = [("'</" ^ name ^ ">'", "ETag to close earlier STag with that name")],
		    start       = start,
		    tail        = tail,
		    peek        = 10,
		    action      = "Pretend tag is an end tag"}));
	   if stag.name = etag.name then
	     return (etag, tail)
	   else
	     {
	      error {kind        = WFC,
		     requirement = "Element Type Match : The Name in an element's end-tag must match the element type in the start-tag.",
		     problem     = "Unexpected end tag: '</" ^ (string etag.name) ^ ">'",
		     expected    = [("'</" ^ name ^ ">'", "ETag to close earlier STag with that name")],
		     start       = start,
		     tail        = tail,
		     peek        = 0,
		     action      = "Interpolate missing close tag for " ^ name};
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
		      problem     = "Element content terminated, but no end tag followed.", 
		      expected    = [("'</" ^ name ^ ">'", "ETag to close earlier STag with that name")],
		      start       = start,
		      tail        = tail,
		      peek        = 10,
		      action      = "Immediate failure"}
	 }

endspec