(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD AttListDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: Attribute-list declarations specify the name, data type, and default value
  %%   (if any) of each attribute associated with a given element type:]
  %%
  %%   [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
  %%
  %%   [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %%                                                             [VC: ID Attribute Default] (implicit)
  %%
  %%  *[54]  AttType         ::=  StringType | TokenizedType | EnumeratedType
  %%  *[55]  StringType      ::=  'CDATA'
  %%  *[56]  TokenizedType   ::=  'ID'                          *[VC: ID]
  %%                                                            *[VC: One ID per Element Type]
  %%                                                            *[VC: ID Attribute Default]
  %%                            | 'IDREF'                       *[VC: IDREF]
  %%                            | 'IDREFS'                      *[VC: IDREF]
  %%                            | 'ENTITY'                      *[VC: Entity Name]
  %%                            | 'ENTITIES'                    *[VC: Entity Name]
  %%                            | 'NMTOKEN'                     *[VC: Name Token]
  %%                            | 'NMTOKENS'                    *[VC: Name Token]
  %%
  %%  [Definition: Enumerated attributes can take one of a list of values provided in the
  %%   declaration].
  %%
  %%  *[57]  EnumeratedType  ::=  NotationType | Enumeration
  %%
  %%    ==>
  %%
  %%  [K26]  AttType         ::=  'CDATA'
  %%                            | 'ID'                           [VC: ID]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: ID Attribute Default]
  %%                            | 'IDREF'                        [VC: IDREF]
  %%                            | 'IDREFS'                       [VC: IDREF]
  %%                            | 'ENTITY'                       [VC: Entity Name]
  %%                            | 'ENTITIES'                     [VC: Entity Name]
  %%                            | 'NMTOKEN'                      [VC: Name Token]
  %%                            | 'NMTOKENS'                     [VC: Name Token]
  %%                            | NotationType
  %%                            | Enumeration
  %%
  %%   [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')'
  %%
  %%                                                             [VC: Notation Attributes]
  %%                                                             [VC: One Notation Per Element Type]
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %%   [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')'
  %%
  %%                                                             [VC: Enumeration]
  %%
  %%   [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue)
  %%
  %%                                                             [VC:  Required Attribute]
  %%                                                             [VC:  Attribute Default Legal]
  %%                                                             [VC:  Fixed Attribute Default]
  %%
  %%  In an attribute declaration, #REQUIRED means that the attribute must always be provided,
  %%  #IMPLIED that no default value is provided.
  %%
  %%  [Definition: If the declaration is neither #REQUIRED nor #IMPLIED, then the AttValue value
  %%   contains the declared default value; the #FIXED keyword states that the attribute must
  %%   always have the default value. If a default value is declared, when an XML processor
  %%   encounters an omitted attribute, it is to behave as though the attribute were present with
  %%   the declared default value.]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
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
	      probe (tail,  att_def::rev_att_defs)
	    | _ ->
	      {
	       (w2, tail) <- parse_WhiteSpace tail;
	       case tail of
		 | 62 :: tail ->
		   %% '>'
		   return ({w1   = w1,
			    name = name,
			    defs = reverse rev_att_defs,
			    w2   = w2},
			   tail)
		 | char :: _ ->
		   {
		    error {kind        = Syntax,
			   requirement = "ATTLIST decl in DTD must terminate with '>'.",
			   start       = start,
			   tail        = tail,
			   peek        = 10,
			   we_expected = [("'>'", "to terminate decl")],
			   but         = (describe_char char) ^ " was seen instead",
			   so_we       = "pretend interpolated '>' was seen"};
		    return ({w1   = w1,
			     name = name,
			     defs = reverse rev_att_defs,
			     w2   = w2},
			    tail)
		    }
		 | _ ->
		   hard_error {kind        = EOF,
			       requirement = "ATTLIST decl in DTD must terminate with '>'.",
			       start       = start,
			       tail        = [],
			       peek        = 0,
			       we_expected = [("'>'", "to terminate decl")],
			       but         = "EOF occurred first",
			       so_we       = "fail immediately"}
		   }}

     in
       probe (tail, [])
      }

  %% -------------------------------------------------------------------------------------------------
  %%   [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %% -------------------------------------------------------------------------------------------------

  def parse_AttDef (start : UChars) : Possible AttDef =
    {
     (w1,       tail) <- parse_WhiteSpace start;
     case tail of

       | 62 :: tail ->
         %% '>'
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
	      return (Some {w1       = w1,
			    name     = name,
			    w2       = w2,
                            att_type = att_type,
			    w3       = w3,
			    default  = default},
		      tail)
	    | _ -> return (None, start)
	     }}

  %% -------------------------------------------------------------------------------------------------
  %%  [K26]  AttType         ::=  'CDATA'
  %%                            | 'ID'                           [VC: ID]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: ID Attribute Default]
  %%                            | 'IDREF'                        [VC: IDREF]
  %%                            | 'IDREFS'                       [VC: IDREF]
  %%                            | 'ENTITY'                       [VC: Entity Name]
  %%                            | 'ENTITIES'                     [VC: Entity Name]
  %%                            | 'NMTOKEN'                      [VC: Name Token]
  %%                            | 'NMTOKENS'                     [VC: Name Token]
  %%                            | NotationType
  %%                            | Enumeration
  %% -------------------------------------------------------------------------------------------------

  def parse_AttType (start : UChars) : Required AttType =
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

      %% can anyone say "S-Expression" ?  Sheesh, this is a botch of a grammar...

      %% EnumeratedType
      | 78 :: 79 :: 84 :: 65 :: 84 :: 73 :: 79 :: 78 :: tail ->
        %% 'NOTATION'
	parse_NotationType tail

      | 40 :: tail ->
        %% open-paren
        parse_Enumeration tail

      | char :: _ ->
	hard_error {kind        = Syntax,
		    requirement = "Attribute Type",
		    start       = start,
		    tail        = start,
		    peek        = 10,
		    we_expected = [("'CDATA'",    "to declare CDATA    attribute"),
				   ("'IDREFS'",   "to declare IDREFS   attribute"),
				   ("'IDREF'",    "to declare IDREF    attribute"),
				   ("'ID'",       "to declare ID       attribute"),
				   ("'ENTITIES'", "to declare ENTITIES attribute"),
				   ("'ENTITY'",   "to declare ENTITY   attribute"),
				   ("'NMTOKENS'", "to declare NMTOKENS attribute"),
				   ("'NMTOKEN '", "to declare NMTOKEN  attribute"),
				   ("'NOTATION'", "to start notationtype"),
				   ("'('",        "to start enumeration")],
		    but         = (describe_char char) ^ " was seen instead",
		    so_we       = "fail immediately"}
      | _ ->
	hard_error {kind        = EOF,
		    requirement = "Attribute Type",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("'CDATA'",    "to declare CDATA    attribute"),
				   ("'IDREFS'",   "to declare IDREFS   attribute"),
				   ("'IDREF'",    "to declare IDREF    attribute"),
				   ("'ID'",       "to declare ID       attribute"),
				   ("'ENTITIES'", "to declare ENTITIES attribute"),
				   ("'ENTITY'",   "to declare ENTITY   attribute"),
				   ("'NMTOKENS'", "to declare NMTOKENS attribute"),
				   ("'NMTOKEN '", "to declare NMTOKEN  attribute"),
				   ("'NOTATION'", "to start notationtype"),
				   ("'('",        "to start enumeration")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}

  %% -------------------------------------------------------------------------------------------------
  %%   [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')'
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
       | 40 :: tail ->
         %% open-paren
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

		 | 124 :: tail ->
                   %% '|'
		   {
		    (w4,   tail) <- parse_WhiteSpace tail;
		    (name, tail) <- parse_Name       tail;
		    probe (tail, Cons ((w3, w4, name), rev_names))
		   }

		 | 41 :: tail ->
                   %% close-paren
		   return (Notation {w1     = w1,
				     w2     = w2,
				     first  = first,
				     others = reverse rev_names,
				     w3     = w3},
			   tail)

		 | char :: _ ->
		   hard_error {kind        = Syntax,
			       requirement = "NOTATION decl uses '|' to separate options.",
			       start       = start,
			       tail        = tail,
			       peek        = 10,
			       we_expected = [("'|'", "to add more options"),
					      ("')'", "to close decl")],
			       but         = (describe_char char) ^ " was seen instead",
			       so_we       = "fail immediately"}

		 | _ ->
		   hard_error {kind        = EOF,
			       requirement = "NOTATION decl uses '|' to separate options.",
			       start       = start,
			       tail        = tail,
			       peek        = 10,
			       we_expected = [("'|'", "to add more options"),
					      ("')'", "to close decl")],
			       but         = "EOF occurred first",
			       so_we       = "fail immediately"}
		  }
	  in
	    probe (tail, [])
	   }
       | char :: _ ->
	   hard_error {kind        = Syntax,
		       requirement = "NOTATION decl in DTD used '(' to initiate options.",
		       start       = start,
		       tail        = tail,
		       peek        = 10,
		       we_expected = [("'('", "to begin enumeration")],
		       but         = (describe_char char) ^ " was seen instead",
		       so_we       = "fail immediately"}
       | _ ->
	   hard_error {kind        = EOF,
		       requirement = "NOTATION decl in DTD used '(' to initiate options.",
		       start       = start,
		       tail        = [],
		       peek        = 0,
		       we_expected = [("'('", "to begin enumeration")],
		       but         = "EOF occurred first",
		       so_we       = "fail immediately"}
	  }

  %% -------------------------------------------------------------------------------------------------
  %%   [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')'
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

	    | 124 :: tail ->
	      %% '|'
	      {
	       (w3,   tail) <- parse_WhiteSpace tail;
	       (name, tail) <- parse_Name       tail;
	       probe (tail, Cons ((w2, w3, name), rev_names))
	      }

	    | 41 :: tail ->
              %% close-paren
	      return (Enumeration {w1     = w1,
				   first  = first,
				   others = reverse rev_names,
				   w2     = w2},
		      tail)

	    | char :: _ ->
	      hard_error {kind        = Syntax,
			  requirement = "Enumeration decl in DTD requires '|' to separate options.",
			  start       = start,
			  tail        = tail,
			  peek        = 10,
			  we_expected = [("'|'", "to continue enumerating"),
					 ("')'", "to terminate enumeration decl")],
			  but         = (describe_char char) ^ " was seen instead",
			  so_we       = "fail immediately"}

	    | _ ->
	      hard_error {kind        = Syntax,
			  requirement = "Enumeration decl in DTD requires '|' to separate options.",
			  start       = start,
			  tail        = tail,
			  peek        = 10,
			  we_expected = [("'|'", "to continue enumerating"),
					 ("')'", "to terminate enumeration decl")],
			  but         = "EOF occurred first",
			  so_we       = "fail immediately"}
	      }
     in
       probe (tail, [])
      }

  %% -------------------------------------------------------------------------------------------------
  %%   [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue)
  %% -------------------------------------------------------------------------------------------------

  def parse_DefaultDecl (start : UChars) : Possible DefaultDecl =
    case start of

      | 35 :: 82 :: 69 :: 81 :: 85 :: 73 :: 82 :: 69 :: 68 :: tail ->
        %% '#REQUIRED'
        return (Some Required, tail)

      | 35 :: 73 :: 77 :: 80 :: 76 :: 73 :: 69 :: 68 :: tail ->
        %% '#IMPLIED'
        return (Some Implied, tail)

      | 35 :: 70 :: 73 :: 88 :: 69 :: 68 :: tail ->
	%% '#FIXED'
	{
	 (w1,    tail) <- parse_WhiteSpace tail;
	 (value, tail) <- parse_AttValue tail;
	 return (Some (Fixed (Some w1, value)),
		 tail)
	}

      | _ ->
	{
	 (value, tail) <- parse_AttValue start;
	 return (Some (Fixed (None, value)),
		 tail)
	}

endspec