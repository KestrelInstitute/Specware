(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD ElementDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: An element type declaration takes the form:]
  %%
  %%   [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>'
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %%  [Definition: An element type has element content when elements of that type must contain only
  %%   child elements (no character data), optionally separated by white space (characters matching
  %%   the nonterminal S).]
  %%
  %%  [Definition: In this case, the constraint includes a content model, a simple grammar governing
  %%   the allowed types of the child elements and the order in which they are allowed to appear.]
  %%
  %%   [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children
  %%
  %%  *[47]  children     ::=  (choice | seq) ('?' | '*' | '+')?
  %%    ==>
  %%  [K20]  children     ::=  cp
  %%                                                             [KWFC: Children Decl]
  %%
  %%  The grammar is built on content particles (cps), which consist of names, choice lists of
  %%  content particles, or sequence lists of content particles:
  %%
  %%  *[48]  cp           ::=  (Name | choice | seq) ('?' | '*' | '+')?
  %%    ==>
  %%  [K21]  cp           ::=  cpbody Repeater
  %%  [K22]  cpbody       ::=  Name | choice | seq
  %%
  %%  *[49]  choice       ::=  '(' S? cp ( S? '|' S? cp )+ S? ')'
  %%    ==>
  %%  [K23]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')'
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%  *[50]  seq          ::=  '(' S? cp ( S? ',' S? cp )* S? ')'
  %%    ==>
  %%  [K24]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')'
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%  [K25]  Repeater     ::=  ('?' | '*' | '+' | '')
  %%
  %%  [Definition: An element type has mixed content when elements of that type may contain
  %%   character data, optionally interspersed with child elements.] In this case, the types of
  %%   the child elements may be constrained, but not their order or their number of occurrences:
  %%
  %%   [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')'
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%                                                             [VC: No Duplicate Types]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>'
  %% -------------------------------------------------------------------------------------------------

  def parse_ElementDecl (start : UChars) : Required ElementDecl =
    %%
    %% We begin here just past '<!ELEMENT' in rule 45, looking for:
    %%
    %%   S Name S contentspec S? '>'
    %%
    {
     (w1,       tail) <- parse_WhiteSpace  start;
     (name,     tail) <- parse_Name        tail;
     (w2,       tail) <- parse_WhiteSpace  tail;
     (contents, tail) <- parse_ContentSpec tail;
     (w3,       tail) <- parse_WhiteSpace  tail;
     case tail of

       | 62 :: tail ->
         %% '>'
         return ({w1       = w1,
		  name     = name,
		  w2       = w2,
		  contents = contents,
		  w3       = w3},
		 tail)

       | _ ->
	 {
	  error {kind        = Syntax,
		 requirement = "An ElementDecl in a DTD must end with '>'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("'>'", "end of ElementDecl in DTD")],
		 but         = "some ElementDecl doesn't end with '>'",
		 so_we       = "pretend interpolated '>' was seen"};
	  return ({w1       = w1,
		   name     = name,
		   w2       = w2,
		   contents = contents,
		   w3       = w3},
		  tail)
	}}

  %% -------------------------------------------------------------------------------------------------
  %%   [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children
  %% -------------------------------------------------------------------------------------------------

  def parse_ContentSpec (start : UChars) : Required ContentSpec =
    case start of

      | 69 :: 77 :: 80 :: 84 :: 89  :: tail ->
        %% 'EMPTY'
        return (Empty, tail)

      | 65 :: 78 :: 89 :: tail ->
	%% 'ANY'
        return (Any, tail)

      | _ ->
        {
	 (possible_mixed, tail) <- parse_Mixed start;
	 case possible_mixed of

	   | Some mixed ->
	     return (Mixed mixed,
		     tail)

	   | _ ->
	     {
	      (children, tail) <- parse_Children start;
	      return (Children children,
		      tail)
	      }}

  %% -------------------------------------------------------------------------------------------------
  %%  [K20]  children     ::=  cp
  %%                                                             [KWFC: Children Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Children Decl]                         [K20] -- well_formed_children?
  %%
  %%    The basic production for children in the contentspec of an elementdecl in the DTD
  %%    must be a choice or seq, not a simple name.
  %% -------------------------------------------------------------------------------------------------

  def parse_Children (start : UChars) : Required Children =
    case start of
      %% test for open-paren to rule out Name option in cp production

      | 40 :: _ ->
        %% '('
        parse_CP start

      | char :: _ ->
	hard_error {kind        = Syntax,
		    requirement = "A children clause in an ElementDecl in a DTD should begin with '(' for a choice or seq.",
		    start       = start,
		    tail        = start,
		    peek        = 10,
		    we_expected = [("'('", "To start description of a choice or sequence")],
		    but         = "a children clause begins with " ^ (describe_char char) ^ " instead",
		    so_we       = "fail immediately"}

      | _ ->
	hard_error {kind        = Syntax,
		    requirement = "A children clause in an ElementDecl in a DTD should begin with '(' for a choice or seq.",
		    start       = start,
		    tail        = start,
		    peek        = 10,
		    we_expected = [("'('", "To start description of a choice or sequence")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}

  %% -------------------------------------------------------------------------------------------------
  %%  [K21]  cp           ::=  cpbody Repeater
  %% -------------------------------------------------------------------------------------------------

  def parse_CP (start : UChars) : Required CP =
    {
     (body,     tail) <- parse_CPBody start;
     (repeater, tail) <- parse_Repeater tail;
     return ({body     = body,
	      repeater = repeater},
	     tail)
     }

  %% -------------------------------------------------------------------------------------------------
  %%  [K22]  cpbody       ::=  Name | choice | seq
  %%  [K23]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')'
  %%  [K24]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')'
  %% -------------------------------------------------------------------------------------------------

  def parse_CPBody (start : UChars) : Required CPBody =
    case start of
      | 40 :: tail ->
        %% '('
        {
	 (w1, tail) <- parse_WhiteSpace tail;
	 (cp, tail) <- parse_CP         tail;
	 (w2, tail) <- parse_WhiteSpace tail;
	 case tail of

	   | 124 :: tail ->
             %% '|'
	     let
	       def probe (tail, rev_alternatives) =
		 {
		  (w3, tail) <- parse_WhiteSpace tail;
		  (cp, tail) <- parse_CP         tail;
		  (w4, tail) <- parse_WhiteSpace tail;
		  let rev_alternatives = Cons ((w3, cp, w4), rev_alternatives) in
		  case tail of

		    | 41 :: tail ->
                      %% ')'
		      return (Choice {alternatives = reverse rev_alternatives},
			      tail)

		    | 124 :: tail ->
		      %% '|'
		      probe (tail, rev_alternatives)
		    | _ ->
		      hard_error {kind        = Syntax,
				  requirement = "A choice in an elementdecl in DTD should continue with '!', or end with ')'.",
				  start       = start,
				  tail        = tail,
				  peek        = 10,
				  we_expected = [("'!'", "indication of choice"),
						 ("')'", "termination of choise")],
				  but         = "Something else occurred first",
				  so_we       = "fail immediately"}
		     }
	     in
	       probe (tail, [(w1, cp, w2)])

	   | 44 :: tail ->
             %% ','
	     let
	       def probe (tail, rev_items) =
		 {
		  (w3, tail) <- parse_WhiteSpace tail;
		  (cp, tail) <- parse_CP         tail;
		  (w4, tail) <- parse_WhiteSpace tail;
		  let rev_items = Cons ((w3, cp, w4), rev_items) in
		  case tail of

		    | 41 :: tail ->
                      %% ')'
		      return (Seq {items = reverse rev_items},
			      tail)
		    | 44 :: tail ->
		      %% ','
		      probe (tail, rev_items)
		    | _ ->
		      hard_error {kind        = Syntax,
				  requirement = "A sequence in an elementdecl in DTD should continue with ',', or end with ')'.",
				  start       = start,
				  tail        = tail,
				  peek        = 10,
				  we_expected = [("','", "indication of sequence"),
						 ("')'", "termination of sequence")],
				  but         = "Something else occurred first",
				  so_we       = "fail immediately"}
		     }
	     in
	       probe (tail, [(w1, cp, w2)])

	   | 41 :: tail ->
	     %% ')'
	     %% second item is optional for Seq, but not Choice
	     return (Seq {items = [(w1, cp, w2)]},
		     tail)

	   | char :: _ ->
	     hard_error {kind        = Syntax,
			 requirement = "A choice or sequence in an elementdecl in DTD should continue with '|' or ',', or end with ')'.",
			 start       = start,
			 tail        = tail,
			 peek        = 10,
			 we_expected = [("'|'", "indication of choice"),
					("','", "indication of sequence"),
					("')'", "termination of choise or sequence")],
			 but         = (describe_char char) ^ " was seen instead",
			 so_we       = "fail immediately"}

	   | _ ->
	     hard_error {kind        = Syntax,
			 requirement = "A choice or sequence in an elementdecl in DTD should continue with '|' or ',', or end with ')'.",
			 start       = start,
			 tail        = tail,
			 peek        = 10,
			 we_expected = [("'|'", "indication of choice"),
					("','", "indication of sequence"),
					("')'", "termination of choise or sequence")],
			 but         = "EOF occurred first",
			 so_we       = "fail immediately"}
	    }

      | _ ->
	{
	 (name, tail) <- parse_Name start;
	 return (Name name,
		 tail)
	 }

  %% -------------------------------------------------------------------------------------------------
  %%  [K25]  Repeater     ::=  ('?' | '*' | '+' | '')
  %% -------------------------------------------------------------------------------------------------

  def parse_Repeater (start : UChars) : Required Repeater =
    %% Note: no whitespace allowed between name or right-paren and '?', '*', or '+'
    case start of
      | 63 (* '?' *) :: tail -> return (ZeroOrOne,  tail)
      | 42 (* '*' *) :: tail ->	return (ZeroOrMore, tail)
      | 43 (* '+' *) :: tail ->	return (OneOrMore,  tail)
      | _ ->                	return (One,       start)

  %% -------------------------------------------------------------------------------------------------
  %%   [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')'
  %% -------------------------------------------------------------------------------------------------
  %%  Note: if the list is empty, it ends with ")", if non-empty, ")*"
  %% -------------------------------------------------------------------------------------------------

  def parse_Mixed (start : UChars) : Possible Mixed =
    case start of
      | 40 :: tail ->
        %% '('
        {
	 (w1, tail) <- parse_WhiteSpace tail;
	 case tail of

	   | 35 :: 80 :: 67 :: 68 :: 65 :: 84 :: 65 :: tail_0 ->
             %% '#PCDATA'
	     {
	      (w2, tail) <- parse_WhiteSpace tail_0;
	      (case w2 of

		 | 41 :: tail ->
                   %% ')'
		   return (Some {w1    = w1,
				 names = [],
				 w2    = w2},
			   tail)

		 | _ ->
		   let
                     def probe (tail, rev_names) =
		       {
			(w3, tail) <- parse_WhiteSpace tail;
			case tail of

			  | 124 :: tail ->
                            %% '|'
			    {
			     (w4,   tail) <- parse_WhiteSpace tail;
			     (name, tail) <- parse_Name        tail;
			     probe (tail, Cons ((w3, w4, name), rev_names))
			    }

			  | 41 :: 42 :: tail ->
                            %% ')*'
			    return (Some {w1    = w1,
					  names = reverse rev_names,
					  w2    = w2},
				    tail)

			  | char :: _ ->
			    {
			     error {kind        = Syntax,
				    requirement = "Mixed construction in elementdecl in DTD requires '|' or ')'.",
				    start       = start,
				    tail        = tail,
				    peek        = 10,
				    we_expected = [("'|'",  "to indicate a new alternative"),
						   ("')*'", "to terminate declaration")],
				    but         = (describe_char char) ^ "was seen instead",
				    so_we       = "pretend interpolated ')*' was seen"};
			     return (Some {w1    = w1,
					   names = reverse rev_names,
					   w2    = w2},
				     (case tail of
					| 41 :: tail -> tail  % skip past close paren
					| _ -> tail))
			    }

			  | _  ->
			    hard_error {kind        = EOF,
					requirement = "Mixed construction in elementdecl in DTD requires '|' or ')'.",
					start       = start,
					tail        = [],
					peek        = 0,
					we_expected = [("'|'",  "to indicate a new alternative"),
						       ("')*'", "to terminate declaration")],
					but         = "EOF occurred first",
					so_we       = "fail immediately"}
			   }
		   in
		     probe (tail_0, []))
		}
	   | _ -> return (None, start)
	    }
      | _ -> return (None, start)

endspec
