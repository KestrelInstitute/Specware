XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Data_Type_Document -- ElementDecl                                                   %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>' 
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %% [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children 
  %%
  %% [47]  children     ::=  (choice | seq) ('?' | '*' | '+')? 
  %%
  %% [48]  cp           ::=  (Name | choice | seq) ('?' | '*' | '+')? 
  %%
  %% [49]  choice       ::=  '(' S? cp ( S? '|' S? cp )+ S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%
  %% [50]  seq          ::=  '(' S? cp ( S? ',' S? cp )* S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %% [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%                                                             [VC: No Duplicate Types]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%
  %% [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>' 
  %%
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
		 start)
       | _ ->
         error ("Expected closing '>' for ElementDecl in DTD", start, tail)
	}

  %%
  %% [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children 
  %%
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
	      (possible_children, tail) <- parse_Children start;
	      case possible_children of
		| Some children ->
		  return (Children children,
			  tail)
		| _ ->
		  error ("No ContentSpec", start, tail)
		 }}
	     

  %%
  %% [51]  Mixed  ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')' 
  %%
  def parse_Mixed (start : UChars) : Possible Mixed =
    case start of
      | 40  (* '(' *) :: tail ->   % paren balancing comment: ')'
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
			  | _  ->
			    {
			     (when true
			      (error ("#PCDATA declaration in DTD containing names must end with ')*'",
				      start, tail)));
			     return (Some (Names {w1    = w1,
						  names = rev rev_names,
						  w2    = w2}),
				     tail)
			    }}
		   in
		     probe (tail_0, []))
		}
	   | _ -> return (None, start)
	    }
      | _ -> return (None, start)
		       

  %%
  %% [47]  children  ::=  (choice | seq) ('?' | '*' | '+')? 
  %%
  op parse_Children : UChars -> Possible Children

  %%
  %% [48]  cp        ::=  (Name | choice | seq) ('?' | '*' | '+')? 
  %%
  op parse_CP : UChars -> Required CP

  %%
  %% [49]  choice    ::=  '(' S? cp ( S? '|' S? cp )+ S? ')' 
  %%
  op parse_Choice : UChars -> Possible Choice


  %%
  %% [50]  seq       ::=  '(' S? cp ( S? ',' S? cp )* S? ')' 
  %%
  op parse_Seq : UChars -> Required Seq

endspec
