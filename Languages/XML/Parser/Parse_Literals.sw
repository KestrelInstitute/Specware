
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
  %%  [11]  SystemLiteral   ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%   ==>
  %% [K23]  SystemuLiteral  ::=  QuotedText
  %%                
  %%  [12]  PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'" 
  %%   ==>
  %% [K24]  PubidLiteral    ::=  QuotedText
  %%                
  %%                                                             [KC: Proper Pubid Literal]   
  %%
  %%  [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def parse_EntityValue (start : UChars) : Required EntityValue =
    let 
       def probe (tail, rev_char_data, rev_items, qchar) =
	 case tail of

	   | 60  (* '<' *)   :: _ -> 
	     error ("'<' is not allowed in an attribute value", start, nthTail (tail, 20))

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
	     error ("Eof while scanning EntityValue", start, [])
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], [], 39)
        | _ ->
          error ("Expected quoted text while scanning EntityValue", start, nthTail (start, 10))

  def parse_AttValue (start : UChars) : Possible AttValue =
    let 
       def probe (tail, rev_char_data, rev_items, qchar) =
	 case tail of

	   | 60  (* '<' *)   :: _ -> 
	     error ("'<' is not allowed in an attribute value", start, nthTail (tail, 20))

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
	     error ("Eof while scanning attribute value", start, [])
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], [], 39)
        | _ ->
	  return (None, start)


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
	     error ("Eof while scanning quoted text", start, [])
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], 39)
        | _ ->
	  error ("Expected quoted text", start, nthTail (start, 10))

  def parse_SystemLiteral (start : UChars) : Required SystemLiteral =
    parse_QuotedText start

  def parse_PubidLiteral (start : UChars) : Required PubidLiteral =
    parse_QuotedText start

endspec
