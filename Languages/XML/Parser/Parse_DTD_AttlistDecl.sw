XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD AttListDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
  %%
  %% [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %%
  %% [54]  AttType         ::=  StringType | TokenizedType | EnumeratedType 
  %%
  %% [55]  StringType      ::=  'CDATA'
  %%
  %% [56]  TokenizedType   ::=    'ID'                           [VC: ID]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: ID Attribute Default]
  %%                            | 'IDREF'                        [VC: IDREF]
  %%                            | 'IDREFS'                       [VC: IDREF]
  %%                            | 'ENTITY'                       [VC: Entity Name]
  %%                            | 'ENTITIES'                     [VC: Entity Name]
  %%                            | 'NMTOKEN'                      [VC: Name Token]
  %%                            | 'NMTOKENS'                     [VC: Name Token]
  %%
  %% [57]  EnumeratedType  ::=  NotationType | Enumeration 
  %%
  %% [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')' 
  %%
  %%                                                             [VC: Notation Attributes] 
  %%                                                             [VC: One Notation Per Element Type] 
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %% [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')' 
  %%
  %%                                                             [VC: Enumeration]
  %%
  %% [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue) 
  %%
  %%                                                             [VC:  Required Attribute] 
  %%                                                             [VC:  Attribute Default Legal]
  %%                                                             [WFC: No < in Attribute Values]
  %%                                                             [VC:  Fixed Attribute Default]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_AttlistDecl (start : UChars) : Required AttlistDecl =
    %%
    %%  We begin here just past '<!ATTLIST' in rule 52, looking for:
    %%
    %%   S Name AttDef* S? '>'
    %%
    {
     (w1,   tail) <- parse_WhiteSpace start;
     (name, tail) <- parse_Name       tail;
     let 
       def probe (tail, rev_att_defs) =
	 {
	  (possible_att_def, tail) <- parse_AttDef tail;
	  case possible_att_def of
	    | Some att_def ->
	      probe (tail, cons (att_def, rev_att_defs))
	    | _ ->
	      {
	       (w2, tail) <- parse_WhiteSpace tail;
	       case tail of
		 | 62  (* '>' *) :: tail ->
		   return ({w1   = w1,
			    name = name,
			    defs = rev rev_att_defs,
			    w2   = w2},
			   tail)
		 | _ ->
		   {
		    error (Surprise {context = "parsing attribute list decl in DTD",
				     expected = [("'>'", "to terminate decl")], 
				     action   = "Pretend '>' was seen",
				     start    = start,
				     tail     = tail,
				     peek     = 10});
		    return ({w1   = w1,
			     name = name,
			     defs = rev rev_att_defs,
			     w2   = w2},
			    tail)
		    }}}
     in
       probe (tail, [])
      }

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_AttDef (start : UChars) : Possible AttDef =
    {
     (w1,       tail) <- parse_WhiteSpace start;
     case tail of
       | 62 (* '>' *) :: tail ->
         return (None, start)
       | _ ->
         {
	  (name,              tail) <- parse_Name        tail;
	  (w2,                tail) <- parse_WhiteSpace  tail;
	  (att_type,          tail) <- parse_AttType     tail;
	  (w3,                tail) <- parse_WhiteSpace  tail;
	  (possible_default,  tail) <- parse_DefaultDecl tail;
	  case possible_default of
	    | Some default ->
	      return (Some {w1      = w1,
			    name    = name,
			    w2      = w2,
                            type    = att_type,
			    w3      = w3,
			    default = default},
		      tail)
	    | _ -> return (None, start)
	     }}

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [54]  AttType         ::=  StringType | TokenizedType | EnumeratedType 
  %%
  %% [55]  StringType      ::=  'CDATA'
  %%
  %% [56]  TokenizedType   ::=    'ID'                           [VC: ID]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: ID Attribute Default]
  %%                            | 'IDREF'                        [VC: IDREF]
  %%                            | 'IDREFS'                       [VC: IDREF]
  %%                            | 'ENTITY'                       [VC: Entity Name]
  %%                            | 'ENTITIES'                     [VC: Entity Name]
  %%                            | 'NMTOKEN'                      [VC: Name Token]
  %%                            | 'NMTOKENS'                     [VC: Name Token]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_AttType (start : UChars) : Required AttType =
    %%
    %% We collapse rules 54,55,56 into one procedure:
    %%
    case start of

      %% StringType

      | 67 :: 68 :: 65 :: 84 :: 65                    (* 'CDATA' *)    :: tail -> return (String,   tail)

      %% TokenizedType

      | 73 :: 68 :: 82 :: 69 :: 70 :: 83              (* 'IDREFS'   *) :: tail -> return (IDRefs,   tail)
      | 73 :: 68 :: 82 :: 69 :: 70                    (* 'IDREF'    *) :: tail -> return (IDRef,    tail)
      | 73 :: 68                                      (* 'ID'       *) :: tail -> return (ID,       tail)
      | 69 :: 78 :: 84 :: 73 :: 84 :: 73 :: 69 :: 83  (* 'ENTITIES' *) :: tail -> return (Entities, tail)
      | 69 :: 78 :: 84 :: 73 :: 84 :: 89              (* 'ENTITY'   *) :: tail -> return (Entity,   tail)
      | 78 :: 77 :: 84 :: 79 :: 75 :: 69 :: 78 :: 83  (* 'NMTOKENS' *) :: tail -> return (NmTokens, tail)
      | 78 :: 77 :: 84 :: 79 :: 75 :: 69 :: 78        (* 'NMTOKEN ' *) :: tail -> return (NmToken,  tail)

      %% EnumeratedType

      | _ ->
        parse_EnumeratedType start
	
  %% -------------------------------------------------------------------------------------------------
  %%
  %% [57]  EnumeratedType  ::=  NotationType | Enumeration 
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_EnumeratedType (start : UChars) : Required AttType =
    %% can anyone say "S-Expression" ?  Sheesh, this is a botch of a grammar...
    case start of
      | 78 :: 79 :: 84 :: 65 :: 84 :: 73 :: 79 :: 78 (* 'NOTATION' *) :: tail ->
        %% [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')' 
	parse_NotationType tail
      | 40 (* open-paren *) :: tail ->
        parse_Enumeration tail
      | _ -> 
	hard_error (Surprise {context = "Parsing DTD",
			      expected = [("'NOTATION'", "to start notationtype"),
					  ("'('",        "to start enumeration")],
			      action   = "Immediate failure",
			      start    = start,
			      tail     = start,
			      peek     = 10})

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')' 
  %%
  %%                                                             [VC: Notation Attributes] 
  %%                                                             [VC: One Notation Per Element Type] 
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_NotationType (start : UChars) : Required AttType =
    %%
    %% We begin here just past 'NOTATION' in rule 58, looking for:
    %%
    %%   S '(' S? Name (S? '|' S? Name)* S? ')' 
    %%
    {
     (w1, tail) <- parse_WhiteSpace start;
     case tail of
       | 40 (* open-paren *) :: tail ->
         %%  S? Name (S? '|' S? Name)* S? ')' 
         {
	  (w2,    tail) <- parse_WhiteSpace tail;
	  (first, tail) <- parse_Name       tail;
	  let 
	    %%  (S? '|' S? Name)* S? ')' 
            def probe (tail, rev_names) =
	      %% '(' S? Name (S? '|' S? Name)* S? ')' 
	      {
	       (w3, tail) <- parse_WhiteSpace tail;
	       case tail of
		 | 124 (* '|' *) :: tail ->
		   {
		    (w4,   tail) <- parse_WhiteSpace tail;
		    (name, tail) <- parse_Name       tail;
		    probe (tail, cons ((w3, w4, name), rev_names))
		   }
		 | 41 (* close-paren *) :: tail ->
		   return (Notation {w1     = w1,
				     w2     = w2,
				     first  = first,
				     others = rev rev_names,
				     w3     = w3},
			   tail)
		 | _ ->
		   hard_error (Surprise {context = "Parsing Enumerated type",
					 expected = [("'|'", "to add more options"),
						     ("')'", "to close decl")],
					 action   = "Immediate failure",
					 start    = start,
					 tail     = tail,
					 peek     = 10})
		  }
	  in
	    probe (tail, [])
	   }
       | _ -> 
	   hard_error (Surprise {context = "Parsing NOTATION decl in DTD",
				 expected = [("'('", "to begin enumeration")],
				 action   = "Immediate failure",
				 start    = start,
				 tail     = tail,
				 peek     = 10})
	  }

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')' 
  %%
  %%                                                             [VC: Enumeration]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Enumeration (start : UChars) : Required AttType =
    %%
    %% We begin here just past '(' in rule 59, looking for:
    %%
    %%  S? Nmtoken (S? '|' S? Nmtoken)* S? ')' 
    %%
    {
     (w1,    tail) <- parse_WhiteSpace start;
     (first, tail) <- parse_Name       tail;
     let 
       def probe (tail, rev_names) =
	 %%  (S? '|' S? Name)* S? ')' 
	 {
	  (w2, tail) <- parse_WhiteSpace tail;
	  case tail of
	    | 124 (* '|' *) :: tail ->
	      {
	       (w3,   tail) <- parse_WhiteSpace tail;
	       (name, tail) <- parse_Name       tail;
	       probe (tail, cons ((w2, w3, name), rev_names))
	      }
	    | 41 (* close-paren *) :: tail ->
	      return (Enumeration {w1     = w1,
				   first  = first,
				   others = rev rev_names,
				   w2     = w2},
		      tail)
	    | _ ->
	      hard_error (Surprise {context = "parsing Enumeration decl in DTD",
				    expected = [("'|'", "to continue enumerating"),
						("')'", "to terminate enumeration decl")],
				    action   = "Immediate failure",
				    start    = start,
				    tail     = tail,
				    peek     = 10})
	     }
     in
       probe (tail, [])
      }
	 
  %% -------------------------------------------------------------------------------------------------
  %%
  %% [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue) 
  %%
  %%                                                             [VC:  Required Attribute] 
  %%                                                             [VC:  Attribute Default Legal]
  %%                                                             [WFC: No < in Attribute Values]
  %%                                                             [VC:  Fixed Attribute Default]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_DefaultDecl (start : UChars) : Possible DefaultDecl =
    case start of
      | 35 :: 82 :: 69 :: 81 :: 85 :: 73 :: 82 :: 69 :: 68 (* '#REQUIRED' *) :: tail ->
        return (Some Required, tail)

      | 35 :: 73 :: 77 :: 80 :: 76 :: 73 :: 69 :: 68       (* '#IMPLIED'  *) :: tail ->
        return (Some Implied, tail)

      | 35 :: 70 :: 73 :: 88 :: 69 :: 68                   (* '#FIXED'    *) :: tail ->
	{
	 (w1, tail)             <- parse_WhiteSpace tail;
	 (possible_value, tail) <- parse_AttValue tail;
	 case possible_value of
	   | Some value ->
	     return (Some (Fixed (Some w1, value)),
		     tail)
	   | _ ->
	     return (None, start)
	    }
      | _ ->
	{
	 (possible_value, tail) <- parse_AttValue start;
	 case possible_value of
	   | Some value ->
	     return (Some (Fixed (None, value)),
		     tail)
	   | _ ->
	     return (None, start)
	    }

endspec