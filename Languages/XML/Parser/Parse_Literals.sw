(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec

  import Parse_References

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Literals                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%    [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %%   [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %%                                                             [WFC: No < in Attribute Values]
  %%
  %%  *[11]  SystemLiteral   ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %%    ==>
  %%  [K37]  SystemuLiteral  ::=  QuotedText
  %%
  %%  *[12]  PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'"
  %%    ==>
  %%  [K38]  PubidLiteral    ::=  QuotedText
  %%                                                             [KWFC: Pubid Literal]
  %%
  %%   [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %%  [K39]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%    [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %% -------------------------------------------------------------------------------------------------

  def parse_EntityValue (start : UChars) : Required EntityValue =
    let
       def probe (tail, rev_char_data, rev_items, qchar) =
	 case tail of

	   | 38 :: tail ->
	     %% '&'
	     {
	      %% parse_Reference assumes we're just past the ampersand.
	      (ref, tail) <- parse_Reference tail;
	      probe (tail,
		     [],
		      Ref ref :: rev_items,
		     qchar)
	     }
	   | 37 :: tail ->
	     %% '%'
             {
	      (ref, tail) <- parse_PEReference tail;
	      probe (tail,
		     [],
		      PERef ref :: rev_items,
		     qchar)}

	   | char :: tail ->
	     if char = qchar then
	       return ({qchar = qchar,
			items = (case rev_char_data of
				   | [] -> reverse rev_items
				   | _ ->
				     reverse (NonRef (reverse rev_char_data) :: rev_items))},
		       tail)
	     else
	       probe (tail,
                      char::rev_char_data,
		      rev_items,
		      qchar)

	   | _ ->
	     hard_error {kind        = EOF,
			 requirement = "A quoted expression was being parsed as the value for an Entity declaration.",
			 start       = start,
			 tail        = start,
			 peek        = 0,
			 we_expected = [("[" ^ (string [qchar]) ^ "] ",
					 (if qchar = 39 then "apostrophe" else "double-quote") ^ "to terminate quoted text")],
			 but         = "EOF occurred before it terminated",
			 so_we       = "fail immediately"}
    in
      case start of
	| 34 :: tail ->
	  %% double-quote
	  probe (tail, [], [], 34)

	| 39 :: tail ->
	  %% apostrophe
	  probe (tail, [], [], 39)

        | char :: _ ->
	  hard_error {kind        = Syntax,
		      requirement = "A quoted expression is needed for the value of an Entity declaration.",
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      we_expected = [("['\"] ", "apostrophe or double-quote to begin quoted text")],   % silly comment to appease emacs: ")
		      but         = (describe_char char) ^ " was seen instead",
		      so_we       = "fail immediately"}

        | _ ->
	  hard_error {kind        = Syntax,
		      requirement = "A quoted expression is needed for the value of an Entity declaration.",
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      we_expected = [("['\"] ", "apostrophe or double-quote to begin quoted text")],   % silly comment to appease emacs: ")
		      but         = "EOF occurred first",
		      so_we       = "fail immediately"}

  %% -------------------------------------------------------------------------------------------------
  %%   [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %%                                                             [WFC: No < in Attribute Values]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: No < in Attribute Values]               [10] [60] [K9] *[41]
  %%
  %%    The replacement text of any entity referred to directly or indirectly in an attribute value
  %%     must not contain a <.
  %%
  %%  TODO
  %% -------------------------------------------------------------------------------------------------

  def parse_AttValue (start : UChars) : Required AttValue =
    let
       def probe (tail, rev_char_data, rev_items, qchar) =
	 case tail of

	   | 60 :: _ ->
	     %% '<'
	     {
	      error {kind        = Syntax,
		     requirement = "'<', '&', and '\"' are not allowed in an attribute value.",            % silly comment to appease emacs: ")
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     we_expected = [("[^<&\"]", "Something other than open-angle, ampersand, or quote")],  % silly comment to appease emacs: ")
		     but         = "'<' was seen",
		     so_we       = "pretend '<' is a normal character"};
	      probe (tail,
		     [60],
                     NonRef (reverse rev_char_data) :: rev_items,
		     qchar)
	     }

	   | 38 :: tail ->
             %% '&'
	     {
	      %% parse_Reference assumes we're just past the ampersand.
	      (ref, tail) <- parse_Reference tail;
	      probe (tail,
		     [],
                     Ref ref :: rev_items,
		     qchar)
	     }

	   | char :: tail ->
	     if char = qchar then
	       let items = (case rev_char_data of
			      | [] -> reverse rev_items
			      | _ ->
			        reverse (NonRef (reverse rev_char_data) :: rev_items)) 
	       in
		 return ({qchar = qchar,
			  items = items,
			  value = compute_attribute_value items},
			 tail)
	     else
	       probe (tail,
                      char::rev_char_data,
		      rev_items,
		      qchar)

	   | _ ->
	     hard_error {kind        = EOF,
			 requirement = "An attribute value was expected.",
 			 start       = start,
			 tail        = tail,
			 peek        = 10,
			 we_expected = [("[" ^ (string [qchar]) ^ "] ",
					 (if qchar = 39 then "apostrophe" else "double-quote") ^ "to terminate quoted text")],
			 but         = "EOF occurred first",
			 so_we       = "fail immediately"}
    in
      case start of

	| 34 :: tail ->
	  %% double-quote
	  probe (tail, [], [], 34)

	| 39 :: tail ->
	  %% apostrophe
          probe (tail, [], [], 39)

        | _ ->
	  hard_error {kind        = Syntax,
		 requirement = "An attribute value was expected.",
		 start       = start,
		 tail        = start,
		 peek        = 10,
		 we_expected = [("...", "quoted text")],
		 but         = "...??...",
		 so_we       = "fail immediately"}

  def compute_attribute_value (items : List AttValue_Item) : UString = % TODO -- use monad state for refs
    foldl (fn (result, item) ->
	   result ++ (case item of
			| NonRef ustr -> ustr
			| Ref    _    -> ustring "<some ref>"))
          []
          items

  %% -------------------------------------------------------------------------------------------------
  %%  [K37]  SystemLiteral   ::=  QuotedText
  %% -------------------------------------------------------------------------------------------------

  def parse_SystemLiteral (start : UChars) : Required SystemLiteral =
    parse_QuotedText start

  %% -------------------------------------------------------------------------------------------------
  %%  [K38]  PubidLiteral    ::=  QuotedText
  %%                                                             [KWFC: Pubid Literal]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Pubid Literal]                         [K38] *[12] -- well_formed_pubid_literal?
  %%
  %%    All chars in a pubid literal are PubidChar's :
  %%    PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'"
  %% -------------------------------------------------------------------------------------------------

  def parse_PubidLiteral (start : UChars) : Required PubidLiteral =
    let
       def find_bad_char tail =
	 case tail of

	   | [] -> None

	   | char :: tail ->
	     if pubid_char? char then
	       find_bad_char tail
	     else
	       Some char
    in
    {
     (qtext, tail) <- parse_QuotedText start;
     case find_bad_char qtext.text of

       | None ->
         return (qtext, tail)

       | Some bad_char ->
	 {
	  (error {kind        = KC,
		  requirement = "Only PubidChar's are allowed in a PubidLiteral.",
		  start       = start,
		  tail        = tail,
		  peek        = 10,
		  we_expected = [("([#x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%])*", "pubid chars")],
		  but         = (describe_char bad_char) ^ " was seen",
		  so_we       = "pretend that is a pubid character"});
	  return (qtext, tail)
	 }}

  %% -------------------------------------------------------------------------------------------------
  %%  [K39]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %% -------------------------------------------------------------------------------------------------

  def parse_QuotedText (start : UChars) : Required QuotedText =
    let
       def probe (tail, rev_text, qchar) =
	 case tail of

	   | char :: tail ->
	     if char = qchar then
	       return ({qchar = qchar,
			text  = reverse rev_text},
		       tail)
	     else
	       probe (tail,
                      char:: rev_text,
		      qchar)

	   | _ ->
	     hard_error {kind        = EOF,
			 requirement = "Quoted text was required.",
			 start       = start,
			 tail        = tail,
			 peek        = 10,
			 we_expected = [("[" ^ (string [qchar]) ^ "] ",
					 (if qchar = 39 then "apostrophe" else "double-quote") ^ "to terminate quoted text")],
			 but         = "EOF occurred first",
			 so_we       = "fail immediately"}
    in
      case start of

	| 34 :: tail ->
          %% double-quote
          probe (tail, [], 34)

	| 39 :: tail ->
          %% apostrophe
	  probe (tail, [], 39)

        | char :: _ ->
	  hard_error {kind        = Syntax,
		      requirement = "Quoted text was required.",
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      we_expected = [("['\"] ", "apostrophe or double-quote to begin quoted text")], % silly comment to appease emacs: ")
		      but         = (describe_char char) ^ " was seen instead",
		      so_we       = "fail immediately"}
        | _ ->
	  hard_error {kind        = Syntax,
		      requirement = "Quoted text was required.",
		      start       = start,
		      tail        = start,
		      peek        = 10,
		      we_expected = [("['\"] ", "apostrophe or double-quote to begin quoted text")], % silly comment to appease emacs: ")
		      but         = "EOF occurred first",
		      so_we       = "fail immediately"}

endspec
