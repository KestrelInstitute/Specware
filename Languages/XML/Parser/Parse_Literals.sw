
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
	     hard_error {kind        = EOF,
			 requirement = "A quoted expression was being parsed as the value for an Entity declaration.",
			 problem     = "EOF occurred before it terminated.",
			 expected    = [("[" ^ (string [qchar]) ^ "] ", 
					 (if qchar = 39 then "apostrophe" else "double-quote") ^ "to terminate quoted text")],
			 start       = start,
			 tail        = start,
			 peek        = 0,
			 action      = "Immediate error"}
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], [], 39)
        | char :: _ ->
	  hard_error {kind        = Syntax,
		      requirement = "A quoted expression is needed for the value of an Entity declaration.",
		      problem     = (describe_char char) ^ " was seen instead.",
		      expected    = [("['\"] ", "apostrophe or double-quote to begin quoted text")],   % silly comment to appease emacs: ")
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      action      = "Immediate error"}
        | _ ->
	  hard_error {kind        = Syntax,
		      requirement = "A quoted expression is needed for the value of an Entity declaration.",
		      problem     = "EOF occurred first.",
		      expected    = [("['\"] ", "apostrophe or double-quote to begin quoted text")],   % silly comment to appease emacs: ")
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      action      = "Immediate error"}

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
	      error {kind        = Syntax,
		     requirement = "'<', '&', and '\"' are not allowed in an attribute value.",            % silly comment to appease emacs: ")
		     problem     = "'<' was seen",
		     expected    = [("[^<&\"]", "Something other than open-angle, ampersand, or quote")],  % silly comment to appease emacs: ")
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     action      = "Treating '<' as normal character"};
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
	     hard_error {kind        = EOF,
			 requirement = "An attribute value was expected.", 
			 problem     = "EOF occurred first.",
			 expected    = [("[" ^ (string [qchar]) ^ "] ", 
					 (if qchar = 39 then "apostrophe" else "double-quote") ^ "to terminate quoted text")],
			 start       = start,
			 tail        = tail,
			 peek        = 10,
			 action      = "Immediate failure"}
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
	     hard_error {kind        = EOF,
			 requirement = "Quoted text was required.",
			 problem     = "EOF occurred first.",
			 expected    = [("[" ^ (string [qchar]) ^ "] ", 
					 (if qchar = 39 then "apostrophe" else "double-quote") ^ "to terminate quoted text")],
			 start       = start,
			 tail        = tail,
			 peek        = 10,
			 action      = "Immediate failure"}
    in
      case start of
	| 34 (* double-quote *) :: tail -> probe (tail, [], 34)
	| 39 (* apostrophe   *) :: tail -> probe (tail, [], 39)
        | char :: _ ->
	  hard_error {kind        = Syntax,
		      requirement = "Quoted text was required.",
		      problem     = (describe_char char) ^ " was seen instead.",
		      expected    = [("['\"] ", "apostrophe or double-quote to begin quoted text")], % silly comment to appease emacs: ")
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      action      = "Immediate error"}
        | _ ->
	  hard_error {kind        = Syntax,
		      requirement = "Quoted text was required.",
		      problem     = "EOF occurred first.",
		      expected    = [("['\"] ", "apostrophe or double-quote to begin quoted text")], % silly comment to appease emacs: ")
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      action      = "Immediate error"}

endspec
