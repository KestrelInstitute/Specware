
XML qualifying spec

  import Parse_References

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Literals                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %%  [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %% *[11]  SystemLiteral   ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%   ==>
  %% [K30]  SystemuLiteral  ::=  QuotedText
  %%                
  %% *[12]  PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'" 
  %%   ==>
  %% [K31]  PubidLiteral    ::=  QuotedText
  %%                
  %%                                                             [KC: Proper Pubid Literal]   
  %%
  %%  [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %% [K32]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%   [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_EntityValue (start : UChars) : Required EntityValue =
    let 
       def probe (tail, rev_char_data, rev_items, qchar) =
	 case tail of

	   | 60  (* '<' *)   :: tail -> 
	     {
	      error (Surprise {context  = "'<' is not allowed in an entity value", 
			       expected = [("[^%&]", "Something other than percent, ampersand, or quote")], 
			       action   = "Treating '<' as normal character",
			       start    = start,
			       tail     = tail,
			       peek     = 10});
	      probe (tail,
		     [60], 
		     cons (NonRef (rev rev_char_data),
			   rev_items),
		     qchar)
	     }

	   | 38  (* '&' *)   :: tail -> 
	     {
	      %% parse_Reference assumes we're just past the ampersand.
	      (ref, tail) <- parse_Reference tail;
	      probe (tail,
		     [], 
		     cons (Ref ref,
			   rev_items), 
		     qchar)
	     }
	   | 37  (* '%' *)   :: tail -> 
             {
	      (ref, tail) <- parse_PEReference tail;
	      probe (tail,
		     [], 
		     cons (PERef ref,
			   rev_items), 
		     qchar)}

	   | char :: tail -> 
	     if char = qchar then
	       return ({qchar = qchar,
			items = (case rev_char_data of
				   | [] -> rev rev_items
				   | _ -> 
				     rev (cons (NonRef (rev rev_char_data),
						rev_items)))},
		       tail)
	     else
	       probe (tail,
		      cons (char, rev_char_data), 
		      rev_items,
		      qchar)
	   | _ ->
	     hard_error (EOF {context = "Parsing EntityValue", 
			      start   = start})
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], [], 39)
        | _ ->
	  hard_error (Surprise {context = "About to parse quoted text while scanning EntityValue", 
				expected = [("['\"] ", "apostrophe or double-quote to begin quoted text")],
				action   = "Immediate error",
				start    = start,
				tail     = start,
				peek     = 10})

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_AttValue (start : UChars) : Possible AttValue =
    let 
       def probe (tail, rev_char_data, rev_items, qchar) =
	 case tail of

	   | 60  (* '<' *)   :: _ -> 
	     {
	      error (Surprise {context  = "'<' is not allowed in an attribute value", 
			       expected = [("[^<&]", "Something other than open-angle, ampersand, or quote")], 
			       action   = "Treating '<' as normal character",
			       start    = start,
			       tail     = tail,
			       peek     = 10});
	      probe (tail,
		     [60], 
		     cons (NonRef (rev rev_char_data),
			   rev_items),
		     qchar)
	     }

	   | 38  (* '&' *)   :: tail -> 
	     {
	      %% parse_Reference assumes we're just past the ampersand.
	      (ref, tail) <- parse_Reference tail;
	      probe (tail,
		     [], 
		     cons (Ref ref,
			   rev_items), 
		     qchar)
	     }
	   | char :: tail -> 
	     if char = qchar then
	       return (Some {qchar = qchar,
			     items = (case rev_char_data of
					| [] -> rev rev_items
					| _ -> 
					  rev (cons (NonRef (rev rev_char_data),
						     rev_items)))},
		       tail)
	     else
	       probe (tail,
		      cons (char, rev_char_data), 
		      rev_items,
		      qchar)
	   | _ ->
	     hard_error (EOF {context = "Parsing attribute value", 
			      start   = start})
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], [], 39)
        | _ ->
	  return (None, start)

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K30]  SystemuLiteral  ::=  QuotedText
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_SystemLiteral (start : UChars) : Required SystemLiteral =
    parse_QuotedText start

  %% -------------------------------------------------------------------------------------------------
  %%                
  %% [K31]  PubidLiteral    ::=  QuotedText
  %%                
  %%                                                             [KC: Proper Pubid Literal]   
  %%
  %%  [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_PubidLiteral (start : UChars) : Required PubidLiteral =
    parse_QuotedText start

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K32]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_QuotedText (start : UChars) : Required QuotedText =
    let 
       def probe (tail, rev_text, qchar) =
	 case tail of
	   | char :: tail -> 
	     if char = qchar then
	       return ({qchar = qchar,
			text  = rev rev_text},
		       tail)
	     else
	       probe (tail,
		      cons (char, rev_text),
		      qchar)
	   | _ ->
	     hard_error (EOF {context = "scanning quoted text", 
			      start   = start})
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], 39)
        | _ ->
	  hard_error (Surprise {context  = "About to parse quoted text",
				expected = [("['\"] ", "apostrophe or double-quote to begin quoted text")],
				action   = "Immediate error",
				start    = start,
				tail     = start,
				peek     = 10})

endspec
