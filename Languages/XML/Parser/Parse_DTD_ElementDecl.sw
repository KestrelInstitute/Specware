XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD ElementDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>' 
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %%  [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children 
  %%
  %%  [47]  children     ::=  (choice | seq) ('?' | '*' | '+')? 
  %%
  %%
  %% *[48]  cp           ::=  (Name | choice | seq) ('?' | '*' | '+')? 
  %%   ==>
  %% [K17]  cp           ::=  cpbody ('?' | '*' | '+')? 
  %% [K18]  cpbody       ::=  Name | choice | seq
  %%
  %% *[49]  choice       ::=  '(' S? cp ( S? '|' S? cp )+ S? ')' 
  %%   ==>
  %% [K19]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%
  %% *[50]  seq          ::=  '(' S? cp ( S? ',' S? cp )* S? ')' 
  %%   ==>
  %% [K20]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%  [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%                                                             [VC: No Duplicate Types]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>' 
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
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
       | 62 (* '>' *) :: tail ->
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
  %%
  %%  [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_ContentSpec (start : UChars) : Required ContentSpec =
    case start of
      | 69 :: 77 :: 80 :: 84 :: 89  (* 'EMPTY' *) :: tail ->
        return (Empty, tail)
      | 65 :: 78 :: 89              (* 'ANY' *)   :: tail ->
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
  %%
  %%  [47]  children     ::=  (choice | seq) ('?' | '*' | '+')? 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Children (start : UChars) : Required Children =
    case start of
      %% test for open-paren to rule out Name option in cp production
      | 60 (* open-paren *) :: tail ->
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
  %%
  %% [K17]  cp           ::=  cpbody ('?' | '*' | '+')? 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_CP (start : UChars) : Required CP =
    {
     (body, tail) <- parse_CPBody start;
     %% Note: no whitespace allowed between name or right-paren and '?', '*', or '+'
     case tail of
       | 63 (* '?' *) :: tail ->
         return ({body = body,
		  rule = ZeroOrOne},
		 tail)
       | 42 (* '*' *) :: tail ->
         return ({body = body,
		  rule = ZeroOrMore},
		 tail)
       | 43 (* '+' *) :: tail ->
         return ({body = body,
		  rule = OneOrMore},
		 tail)
       | _ ->
         return ({body = body,
		  rule = One},
		 tail)
	}
     
  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K18]  cpbody       ::=  Name | choice | seq
  %% [K19]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')' 
  %% [K20]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_CPBody (start : UChars) : Required CPBody =
    case start of
      | 40 (* open-paren *) :: tail ->
        {
	 (w1, tail) <- parse_WhiteSpace tail;
	 (cp, tail) <- parse_CP         tail;
	 (w2, tail) <- parse_WhiteSpace tail;
	 case tail of
	   | 124 (* '|' *) :: tail ->
	     let 
	       def probe (tail, rev_alternatives) =
		 {
		  (w3, tail) <- parse_WhiteSpace tail;
		  (cp, tail) <- parse_CP         tail;
		  (w4, tail) <- parse_WhiteSpace tail;
		  let rev_alternatives = cons ((w3, cp, w4), rev_alternatives) in
		  case tail of 
		    | 41 (* close-paren *) :: tail ->
		      return (Choice {alternatives = rev rev_alternatives},
			      tail)
		    | _ ->
		      probe (tail, rev_alternatives)
		     }
	     in
	       probe (tail, [(w1, cp, w2)])
	   | 44 (* ',' *) :: tail ->
	     let 
	       def probe (tail, rev_items) =
		 {
		  (w3, tail) <- parse_WhiteSpace tail;
		  (cp, tail) <- parse_CP         tail;
		  (w4, tail) <- parse_WhiteSpace tail;
		  let rev_items = cons ((w3, cp, w4), rev_items) in
		  case tail of 
		    | 41 (* close-paren *) :: tail ->
		      return (Seq {items = rev rev_items},
			      tail)
		    | _ ->
		      probe (tail, rev_items)
		     }
	     in
	       probe (tail, [(w1, cp, w2)])

	   | 41 (* close-paren  *) :: tail ->
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
  %%
  %% [51]  Mixed  ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%                                                             [VC: No Duplicate Types]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Mixed (start : UChars) : Possible Mixed =
    case start of
      | 40  (* open-paren *) :: tail -> 
        {
	 (w1, tail) <- parse_WhiteSpace tail;
	 case tail of
	   | 35 :: 80 :: 67 :: 68 :: 65 :: 84 :: 65 (* '#PCDATA' *) :: tail_0 ->
	     {
	      (w2, tail) <- parse_WhiteSpace tail_0;
	      (case w2 of
		 | 41 (* close-paren *) :: tail ->
		   return (Some (NoNames {w1 = w1,
					  w2 = w2}),
			   tail)
		 | _ ->
		   let
                     def probe (tail, rev_names) =
		       {
			(w3, tail) <- parse_WhiteSpace tail;
			case tail of
			  | 124 (* '|' *) :: tail ->
			    {
			     (w4,   tail) <- parse_WhiteSpace tail;
			     (name, tail) <- parse_Name        tail;
			     probe (tail, cons ((w3, w4, name), rev_names))
			    }
			  | 41 :: 42 (* close-paren star *) :: tail ->
			    return (Some (Names {w1    = w1,
						 names = rev rev_names,
						 w2    = w2}),
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
			     return (Some (Names {w1    = w1,
						  names = rev rev_names,
						  w2    = w2}),
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
