
XML qualifying spec

  import Parse_GenericTag
  import Parse_Character_Data

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Element                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% [39]  element  ::=  EmptyElemTag | STag content ETag 
  %%                                                             [WFC: Element Type Match] 
  %%                                                             [VC:  Element Valid]
  %%
  %% [40]  STag          ::=  '<' Name (S Attribute)* S? '>' 
  %% 
  %%                                                             [WFC: Unique Att Spec]
  %% [41]  Attribute     ::=  Name Eq AttValue 
  %%
  %%                                                             [VC:  Attribute Value Type]
  %%                                                             [WFC: No External Entity References]
  %%                                                             [WFC: No < in Attribute Values]
  %%
  %% [42]  ETag          ::=  '</' Name S? '>'
  %%
  %% [43]  content       ::=  CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
  %% 
  %% [44]  EmptyElemTag  ::=  '<' Name (S Attribute)* S? '/>' 
  %% 
  %%                                                             [WFC: Unique Att Spec]
  %%
  %% ----------------------------------------------------------------------------------------------------

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
	      (error ("Mismatch: \n   Open: " ^ (string open_tag.name) ^ "\n  Close: " ^ (string etag.name),
		      start, tail)));
	     return (Some (Full {stag    = open_tag, 
				 content = content, 
				 etag    = etag}),
		     tail)
	    })
       | _ ->
	 return (None, start)
	}

  op parse_OpenTag : UChars -> Possible GenericTag

  def parse_OpenTag (start : UChars) : Possible GenericTag =
    { (possible_tag, tail) <- parse_Option_GenericTag start;
      case possible_tag of
	| Some tag ->
	  {
	   (when (~ ((start_tag? tag) or (empty_tag? tag)))
	    (error ("Expected an STag or EmptyElemTag", start, tail)));
	   return (possible_tag, tail)}
	| _ -> return (None, start)
     }

  op print_STag : STag -> UString
  op print_ETag : ETag -> UString

  %% ----------------------------------------------------------------------------------------------------

  def parse_Content (start : UChars) : Required Content =
    let 
       def parse_items (tail, rev_result) =
	  {
	   (possible_item, scout) <- parse_Content_Item tail;
	   case possible_item of
	     | Some item ->
	       let (char_data, scout) = parse_CharData scout in
	       parse_items (scout,
			    cons ((item, char_data),
				  rev_result))
	     | _ -> 
	       return (rev rev_result, 
		       tail)
	       }
    in
      let (char_data, tail) = parse_CharData start in
      {
       (items, tail) <- parse_items (tail, []);
       return ({prelude = char_data,
		items   = items},
	       tail)
      }

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
      | 60 (* < *) :: tail ->
        (case tail of
	   | 33 :: 45 :: 45  :: tail -> 
 	     %% "<!--"
	     {
	      %% parse_Comment assumes we're past "<!--"
	      (comment, tail) <- parse_Comment tail; 
	      return (Some (Comment comment),
		      tail)
	     }
	   | 33 :: 91  :: 67 :: 68 :: 65 :: 84 :: 65 :: 91 :: tail ->
	     %% "<![CDATA["
	     {
	      %% parse_Comment assumes we're past "<![CDATA["
	      (cdsect, tail) <- parse_CDSect tail;   
	      return (Some (CDSect cdsect),
		      tail)
	     }
	   | 47 :: _ -> 
	     %% "</"
	     %% start of an ETag, so not something we're looking for
	     return (None, start)
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
	error ("EOF scanning content of element.", start, [])
      | _ ->
	{
	 %% parse_Reference assumes we're back at the (non-"<") start
	 (possible_reference, tail) <- parse_Reference start;
	 return (case possible_reference of
		   | Some ref ->
		     (Some (Reference ref),
		      tail)
		   | _ ->	 
		     (None, start))
	}


  %% ----------------------------------------------------------------------------------------------------
  %% [42]  ETag  ::=  '</' Name S? '>'
  %% ----------------------------------------------------------------------------------------------------

  def parse_ETag (start : UChars) : Required ETag =
    { (possible_tag, tail) <- parse_Option_GenericTag start;
      case possible_tag of
	| Some tag ->
	  {
	   (when (~ (end_tag? tag))
	    (error ("Expected an ETag", start, tail)));
	   return (tag,tail)
	   }
	| _ -> 
	  error ("Expected an ETag, but at least a generic tag", 
		 start, tail)
	 }

endspec