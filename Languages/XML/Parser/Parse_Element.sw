
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

  def parse_Element (start : UChars) : Possible Element =
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
	     (content, tail) <- parse_Content tail;
	     (etag,    tail) <- parse_ETag    tail;
	     (when (~ (open_tag.name = etag.name))
	      (error (WFC {description = "Mismatch: \n   Open: " ^ (string open_tag.name) ^ "\n  Close: " ^ (string etag.name)})));
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
	   (when (end_tag? tag)
	    (error (WFC {description = "Expected an STag or EmptyElemTag, but saw closing tag: " ^ (string tag.name)})));
	   (when (~ ((start_tag? tag) or (empty_tag? tag)))
	    (error (WFC {description = "Expected an STag or EmptyElemTag, but saw unrecognized tag: " ^ (string tag.name)})));
	   return (possible_tag, tail)}
	| _ -> return (None, start)
     }

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K27]  content       ::=  content_item* CharData?
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Content (start : UChars) : Required Content =
    let 
       def parse_items (tail, rev_items) =
	 let (char_data, tail) = parse_CharData tail in
	 {
	  (possible_item, scout) <- parse_Content_Item tail;
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

  def parse_Content_Item (start : UChars) : Possible Content_Item =
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
	     %% pase_PI assumes we're past '<?'
	     {
	      (pi, tail) <-  parse_PI tail;
	      return (Some (PI pi),
		      tail)
	      }
	   | _ ->
	     {
	      %% parse_Element assumes we're back at the original "<"
	      (possible_element, tail) <- parse_Element start; 
	      case possible_element of
		| Some element ->
		  return (Some (Element element),
			  tail)
		| _ ->
		  return (None, start)
	      })
      | [] ->
	hard_error (EOF {context = "parsing content of element",
			 start   = start})
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

  def parse_ETag (start : UChars) : Required ETag =
    { (possible_tag, tail) <- parse_Option_ElementTag start;
      case possible_tag of
	| Some tag ->
	  {
	   (when (~ (end_tag? tag))
	    (error (Surprise {context = "parsing ETag",
			      expected = [("</ ...>", "an ending tag")],
			      action   = "Pretend tag is an end tag",
			      start    = start,
			      tail     = tail,
			      peek     = 10})));
	   return (tag,tail)
	   }
	| _ -> 
	  hard_error (Surprise {context = "parsing ETag",
				expected = [("< ...>", "some kind of element tag")],
				action   = "Immediate failure",
				start    = start,
				tail     = tail,
				peek     = 10})
	 }

endspec