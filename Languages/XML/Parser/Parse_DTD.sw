
XML qualifying spec

  import Parse_DTD_ElementDecl
  import Parse_DTD_AttlistDecl
  import Parse_DTD_EntityDecl    % includes parse_NotationDecl
  import Parse_PI

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD (Doc Type Decl)                                                                 %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% The doctypedecl (DTD) has the following form, 
  %%  <!DOCTYPE     ..>
  %%
  %% It may contain the following atomic markup decls:
  %%
  %%  <!ELEMENT    ...>
  %%  <!ATTLIST    ...>
  %%  <!ENTITY     ...>
  %%  <!NOTATATION ...>
  %%
  %%  [28]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>' 
  %%   ==>
  %% [K15]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? markups? '>' 
  %% [K16]  markups      ::=  '[' (markupdecl | DeclSep)* ']' S?
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%
  %% [28a]  DeclSep      ::=  PEReference | S    
  %%
  %%                                                             [WFC: PE Between Declarations]
  %%
  %%  [29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 
  %%
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %%                                                             [WFC: PEs in Internal Subset]
  %% 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %% 
  %% [K15]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? markups? '>' 
  %% 
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %% 
  %% -------------------------------------------------------------------------------------------------

  def parse_DocTypeDecl (start : UChars) : Required DocTypeDecl =
   %%
   %% We begin here just past '<!DOCTYPE' in rule 28, looking for:
   %%
   %%  S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>' 
   %%
   {
    (w1,          tail) <- parse_WhiteSpace start;
    (name,        tail) <- parse_Name       tail;
    (wx,          tail) <- parse_WhiteSpace tail;
    case tail of
      | 91 (* open-square-bracket *) :: _ ->
        {
	 (markups,     tail) <- parse_markups    tail;
	 case tail of
	   | 62 (* '>' *) :: tail ->
	     return ({w1          = w1,
		      name        = name,
		      external_id = None,
		      w3          = wx,
		      markups     = markups},
		     tail)
	   | char :: _ ->
	     {
	      error {kind         = Syntax,
		     requirement  = "DTD must terminate with '>'.",
		     problem      = (describe_char char) ^ " was unexpected.",
		     expected     = [("'>'", "to terminate DTD")],
		     start        = start,
		     tail         = tail,
		     peek         = 10,
		     action       = "Pretend '>' was seen"};
	      return ({w1          = w1,
		       name        = name,
		       external_id = None,
		       w3          = wx,
		       markups     = markups},
		      tail)
	      }
	   | _ ->
	     hard_error {kind         = Syntax,
			 requirement  = "DTD must terminate with '>'.",
			 problem      = "EOF occurred first.",
			 expected     = [("'>'", "to terminate DTD")],
			 start        = start,
			 tail         = tail,
			 peek         = 10,
			 action       = "Pretend '>' was seen"}
	    }
      | _ ->
	{
	 (external_id, tail) <- parse_ExternalID tail;
	 (w3,          tail) <- parse_WhiteSpace tail;
	 (markups,     tail) <- parse_markups    tail;
	 case tail of
	   | 62 (* '>' *) :: tail ->
	     return ({w1          = w1,
		      name        = name,
		      external_id = Some (wx, external_id),
		      w3          = w3,
		      markups     = markups},
		     tail)
	   | char :: _ ->
	     {
	      error {kind        = Syntax,
		     requirement = "DTD must terminate with '>'.",
		     problem     = (describe_char char) ^ " was unexpected.",
		     expected    = [("'>'", "to terminate DTD")],
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     action      = "Pretend '>' was seen"};
	      return ({w1          = w1,
		       name        = name,
		       external_id = Some (wx, external_id),
		       w3          = w3,
		       markups     = markups},
		      tail)
	      }
	   | _ ->
	      hard_error {kind        = Syntax,
		     requirement  = "DTD must terminate with '>'.",
		     problem      = "EOF occurred first.",
		     expected    = [("'>'", "to terminate DTD")],
		     start       = start,
		     tail        = [],
		     peek        = 0,
		     action      = "Pretend '>' was seen"}
	      }}

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [K16]  markups      ::=  '[' (markupdecl | DeclSep)* ']' S?
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%
  %% [28a]  DeclSep      ::=  PEReference | S    
  %%
  %%                                                             [WFC: PE Between Declarations]
  %%
  %%  [29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 
  %%
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %%                                                             [WFC: PEs in Internal Subset]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_markups (start : UChars) : Possible (List (| Decl MarkupDecl | Sep DeclSep) * WhiteSpace) =
    %%
    %% We begin here with '[' pending in rule 28, looking for:
    %%
    %%   '[' (markupdecl | DeclSep)* ']' S? '>' 
    %%
    %% We handle both [28a] and [29] in one procedure:
    %%
    case start of
      | 91 (* open-square-bracket *) :: tail ->                    
        (let 
            def probe (tail, rev_markups) =
	      case tail of

		| 93 (* close-square-bracket *) :: tail -> 
		  {
		   (w1, scout) <- parse_WhiteSpace tail;
		   return (Some (rev rev_markups, w1),
			   tail)
		   }

                %% [29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 

		| 60 :: 33 :: 69 :: 76 :: 69 :: 77 :: 69 :: 78 :: 84 (* '<!ELEMENT'    *) :: tail -> 
		  {
		   (decl, tail) <- parse_ElementDecl tail;
		   probe (tail, cons (Decl (Element decl), rev_markups))
		  }
		  
		| 60 :: 33 :: 65 :: 84 :: 84 :: 76 :: 73 :: 83 :: 84 (* '<!ATTLIST'    *) :: tail -> 
		  {
		   (decl, tail) <- parse_AttlistDecl tail;
		   probe (tail, cons (Decl (Attributes decl), rev_markups))
		  }
		  
		| 60 :: 33 :: 69 :: 78 :: 84 :: 73 :: 84 :: 89       (* '<!ENTITY'     *) :: tail -> 
		  {
		   (decl, tail) <- parse_EntityDecl tail;
		   probe (tail, cons (Decl (Entity decl), rev_markups))
		  }
		  
		| 60 :: 33 :: 78 :: 79 :: 84 :: 65 :: 84 :: 65 :: 84 :: 73 :: 79 :: 78 (* '<!NOTATATION' *) :: tail -> 
		  {
		   (decl, tail) <- parse_NotationDecl tail;
		   probe (tail, cons (Decl (Notation decl), rev_markups))
		  }
		  
		| 60 :: 63 (* '<?' *) :: tail ->
		  {
		   (decl, tail) <- parse_PI tail;
		   probe (tail, cons (Decl (PI decl), rev_markups))
		  }
		  
		| 60 :: 45 :: 45 (* '<--' *) :: tail ->
		  {
		   (comment, tail) <- parse_Comment tail;
		   probe (tail, cons (Decl (Comment comment), rev_markups))
		  }
		  
                %% [28a] DeclSep      ::=  PEReference | S    

		| 37 (* '%' *) :: tail ->
		  {
		   (ref, tail) <- parse_PEReference tail;
		   probe (tail, cons (Sep (PEReference ref), rev_markups))
		  }
		  
		| char :: _ ->
		  if white_char? char then
		    {
		     (w1, scout) <- parse_WhiteSpace tail;
		     probe (tail, cons (Sep (WhiteSpace w1), rev_markups))
		    }
		  else
		    hard_error {kind        = Syntax,
				requirement = "markup or declsep in DTD must be one of those indicated below.",
				problem     = (describe_char char) ^ " was unexpected.",
				expected    = [("'<!ELEMENT'",            "element decl"),
					       ("'<!ATTLIST'",            "attribute list decl"),
					       ("'<!ENTITY'",             "entity decl"),					       
					       ("'<!NOTATION'",           "notation decl"),					       
					       ("'<--'",                  "comment"),
					       ("'%'",                    "PE Reference"),
					       ("( #9 | #A | #D | #20 )", "whitespace"),
					       ("']'",                    "end of markups in DTD")],
				start       = start,
				tail        = tail,
				peek        = 10,
				action      = "Immediate failure"}
		| _ ->
		    hard_error {kind        = EOF,
				requirement = "markup or declsep in DTD must be one of those indicated below.",
				problem     = "EOF occurred first.",
				expected    = [("'<!ELEMENT'",            "element decl"),
					       ("'<!ATTLIST'",            "attribute list decl"),
					       ("'<!ENTITY'",             "entity decl"),					       
					       ("'<!NOTATION'",           "notation decl"),					       
					       ("'<--'",                  "comment"),
					       ("'%'",                    "PE Reference"),
					       ("( #9 | #A | #D | #20 )", "whitespace"),
					       ("']'",                    "end of markups in DTD")],
				start       = start,
				tail        = [],
				peek        = 0,
				action      = "immediate failure"}
	 in
	   probe (tail, []))
	
      | _ -> return (None, start)

  %% ------------------------------------------------------------------------------------------------

  def parse_ExternalID (start : UChars) : Required ExternalID =  % TODO
    {
     (id, tail) <- parse_GenericID start;
     (when (~ (external_id? id))
      (error {kind        = Syntax,
	      requirement = "external ID must contain a system literal.",
	      problem     = "external ID does not contain system literal.",
	      expected    = [("'SYSTEM \"...\"'",         "id with system literal"),
			     ("'PUBLIC \"...\" \"...\"'", "id with public literal and system literal")],
	      start       = start,
	      tail        = tail,
	      peek        = 10,
	      action      = "Pretend it's ok"}));
     return (id, tail)
    }

endspec
