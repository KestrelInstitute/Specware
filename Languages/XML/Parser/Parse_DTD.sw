
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
  %%  *[28]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>' 
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%
  %% *[28a]  DeclSep      ::=  PEReference | S    
  %%                                                             [WFC: PE Between Declarations]
  %%
  %%  *[29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 
  %%
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %%                                                             [WFC: PEs in Internal Subset]
  %%    ==>
  %%  [K16]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? DTD_Decls? '>' 
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%                                                             [WFC: PE Between Declarations]
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %%
  %%  [K17]  DTD_Decls    ::=  '[' (DTD_Decl)* ']' S?
  %%  [K18]  DTD_Decl     ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S
  %%
  %%                                                             [WFC: PEs in Internal Subset]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %% 
  %%  [K16]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? DTD_Decls? '>' 
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%                                                             [WFC: PE Between Declarations]
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %% 
  %% -------------------------------------------------------------------------------------------------

  def parse_DocTypeDecl (start : UChars) : Required DocTypeDecl =
   %%
   %% We begin here just past '<!DOCTYPE' in [K15] :
   %%
   %%  [K15]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? DTD_Decls '>' 
   %%
   {
    (w1,          tail) <- parse_WhiteSpace start;
    (name,        tail) <- parse_Name       tail;
    (wx,          tail) <- parse_WhiteSpace tail;
    case tail of
      | 91 (* open-square-bracket *) :: _ ->
        {
	 (decls,     tail) <- parse_DTD_Decls tail;
	 case tail of
	   | 62 (* '>' *) :: tail ->
	     return ({w1          = w1,
		      name        = name,
		      external_id = None,
		      w2          = wx,
		      decls       = decls},
		     tail)
	   | char :: _ ->
	     {
	      error {kind        = Syntax,
		     requirement = "DTD must terminate with '>'.",
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     we_expected = [("'>'", "to terminate DTD")],
		     but         = (describe_char char) ^ " was seen instead",
		     so_we       = "pretend interpolated '>' was seen"};
	      return ({w1          = w1,
		       name        = name,
		       external_id = None,
		       w2          = wx,
		       decls       = decls},
		      tail)
	      }
	   | _ ->
	     hard_error {kind         = Syntax,
			 requirement  = "DTD must terminate with '>'.",
			 start        = start,
			 tail         = tail,
			 peek         = 10,
			 we_expected  = [("'>'", "to terminate DTD")],
			 but          = "EOF occurred first",
			 so_we        = "fail immediately"}

	    }
      | _ ->
	{
	 (external_id, tail) <- parse_ExternalID tail;
	 (w2,          tail) <- parse_WhiteSpace tail;
	 (decls,       tail) <- parse_DTD_Decls  tail;
	 case tail of
	   | 62 (* '>' *) :: tail ->
	     return ({w1          = w1,
		      name        = name,
		      external_id = Some (wx, external_id),
		      w2          = w2,
		      decls       = decls},
		     tail)
	   | char :: _ ->
	     {
	      error {kind        = Syntax,
		     requirement = "DTD must terminate with '>'.",
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     we_expected = [("'>'", "to terminate DTD")],
		     but         = (describe_char char) ^ " was seen instead",
		     so_we       = "pretend interpolated '>' was seen"};
	      return ({w1          = w1,
		       name        = name,
		       external_id = Some (wx, external_id),
		       w2          = w2,
		       decls       = decls},
		      tail)
	      }
	   | _ ->
	      hard_error {kind        = Syntax,
			  requirement = "DTD must terminate with '>'.",
			  start       = start,
			  tail        = [],
			  peek        = 0,
			  we_expected = [("'>'", "to terminate DTD")],
			  but         = "EOF occurred first",
			  so_we       = "fail immediately"}
	      }}

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K17]  DTD_Decls    ::=  '[' (DTD_Decl)* ']' S?
  %%  [K18]  DTD_Decl     ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S
  %%
  %%                                                             [WFC: PEs in Internal Subset]
  %%
  %%  [WFC: PEs in Internal Subset]                 *[29] [K18] 
  %%
  %%    In the internal DTD subset, parameter-entity references can occur only where markup
  %%    declarations can occur, not within markup declarations. (This does not apply to references
  %%    that occur in external parameter entities or to the external subset.)
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_DTD_Decls (start : UChars) : Possible DTD_Decls =
    %%
    %% We begin here with '[' pending in [K17], looking for:
    %%
    %%   '[' (DTD_Decl)* ']' S?
    %%
    %% We handle both [K17] and [K18] in one procedure:
    %%
    case start of
      | 91 (* open-square-bracket *) :: tail ->                    
        (let 
            def probe (tail, rev_markups) =
	      case tail of

		| 93 (* close-square-bracket *) :: tail -> 
		  {
		   (w1, tail) <- parse_WhiteSpace tail;
		   return (Some {decls = rev rev_markups, 
				 w1    = w1},
			   tail)
		   }

                %% [29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 

		| 60 :: 33 :: 69 :: 76 :: 69 :: 77 :: 69 :: 78 :: 84 (* '<!ELEMENT'    *) :: tail -> 
		  {
		   (decl, tail) <- parse_ElementDecl tail;
		   probe (tail, cons (Element decl, rev_markups))
		  }
		  
		| 60 :: 33 :: 65 :: 84 :: 84 :: 76 :: 73 :: 83 :: 84 (* '<!ATTLIST'    *) :: tail -> 
		  {
		   (decl, tail) <- parse_AttlistDecl tail;
		   probe (tail, cons (Attributes decl, rev_markups))
		  }
		  
		| 60 :: 33 :: 69 :: 78 :: 84 :: 73 :: 84 :: 89       (* '<!ENTITY'     *) :: tail -> 
		  {
		   (decl, tail) <- parse_EntityDecl (tail, false);
		   probe (tail, cons (Entity decl, rev_markups))
		  }
		  
		| 60 :: 33 :: 78 :: 79 :: 84 :: 65 :: 84 :: 65 :: 84 :: 73 :: 79 :: 78 (* '<!NOTATATION' *) :: tail -> 
		  {
		   (decl, tail) <- parse_NotationDecl tail;
		   probe (tail, cons (Notation decl, rev_markups))
		  }
		  
		| 60 :: 63 (* '<?' *) :: tail ->
		  {
		   (decl, tail) <- parse_PI tail;
		   probe (tail, cons (PI decl, rev_markups))
		  }
		  
		| 60 :: 45 :: 45 (* '<--' *) :: tail ->
		  {
		   (comment, tail) <- parse_Comment tail;
		   probe (tail, cons (Comment comment, rev_markups))
		  }
		  
                %% [28a] DeclSep      ::=  PEReference | S    

		| 37 (* '%' *) :: tail ->
		  {
		   (ref, tail) <- parse_PEReference tail;
		   probe (tail, cons (PEReference ref, rev_markups))
		  }
		  
		| char :: _ ->
		  if white_char? char then
		    {
		     (w1, scout) <- parse_WhiteSpace tail;
		     probe (tail, cons (WhiteSpace w1, rev_markups))
		    }
		  else
		    hard_error {kind        = Syntax,
				requirement = "Each markup or declsep in the DTD must be one of those indicated below.",
				start       = start,
				tail        = tail,
				peek        = 10,
				we_expected = [("'<!ELEMENT'",            "element decl"),
					       ("'<!ATTLIST'",            "attribute list decl"),
					       ("'<!ENTITY'",             "entity decl"),					       
					       ("'<!NOTATION'",           "notation decl"),					       
					       ("'<--'",                  "comment"),
					       ("'%'",                    "PE Reference"),
					       ("( #9 | #A | #D | #20 )", "whitespace"),
					       ("']'",                    "end of markups in DTD")],
				but         = (describe_char char) ^ " was seen instead",
				so_we       = "fail immediately"}
		| _ ->
		    hard_error {kind        = EOF,
				requirement = "Each markup or declsep in the DTD must be one of those indicated below.",
				start       = start,
				tail        = [],
				peek        = 0,
				we_expected = [("'<!ELEMENT'",            "element decl"),
					       ("'<!ATTLIST'",            "attribute list decl"),
					       ("'<!ENTITY'",             "entity decl"),					       
					       ("'<!NOTATION'",           "notation decl"),					       
					       ("'<--'",                  "comment"),
					       ("'%'",                    "PE Reference"),
					       ("( #9 | #A | #D | #20 )", "whitespace"),
					       ("']'",                    "end of markups in DTD")],
				but         = "EOF occurred first",
				so_we       = "fail immediately"}
	 in
	   probe (tail, []))
	
      | _ -> return (None, start)

  %% ------------------------------------------------------------------------------------------------

endspec
