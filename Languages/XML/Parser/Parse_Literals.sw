
XML qualifying spec

  import Parse_References

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Literals                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [9]  EntityValue   ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %% [10]  AttValue      ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %% [11]  SystemLiteral ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%
  %% [12]  PubidLiteral  ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'" 
  %%
  %% [13]  PubidChar     ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %% ----------------------------------------------------------------------------------------------------


  def parse_AttValue (start : UChars) : Required AttValue =
    let 
       def probe (tail, rev_char_data, rev_items, qchar) : Required AttValue =
	 case tail of
	   | 60  (* < *)   :: _ -> 
	     error ("'<' is not allowed in an attribute value", start, nthTail (tail, 20))
	   | 38  (* & *)   :: _ -> 
	     {
	      (possible_ref, tail) <- parse_Reference tail;
	      case possible_ref of
		| Some ref ->
		  probe (tail,
			 [], 
			 let item : AttValue_Item = Ref ref in
			 cons (item, rev_items), 
			 qchar)
		| _ ->
		  error ("'&' is not allowed in an attribute value unless it starts a refernce.", 
				      start, nthTail (tail, 20))
		 }
	   | char :: tail -> 
	     if char = qchar then
	       let av : AttValue =
	           {qchar = qchar,
		    items = (case rev_char_data of
			       | [] -> rev rev_items
			       | _ -> 
			         let item : AttValue_Item = NonRef (rev rev_char_data) in
				 rev (cons (item, rev_items)))}
	       in
		 return (av, tail)
	     else
	       probe (tail,
		      cons (char, rev_char_data), 
		      rev_items,
		      qchar)
	   | _ ->
	     error ("Eof while scanning attribute value", start, [])
    in
      case start of
	| 34 (* double quote *) :: tail -> probe (tail, [], [], 34)
	| 39 (* apostrophe" *)  :: tail -> probe (tail, [], [], 39)
        | _ ->
	  error ("Expected an attribute value", start, nthTail (start, 10))

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
	| 34 (* double quote *) :: tail -> probe (tail, [], 34)
	| 39 (* apostrophe" *)  :: tail -> probe (tail, [], 39)
        | _ ->
	  error ("Expected quoted text", start, nthTail (start, 10))

endspec
