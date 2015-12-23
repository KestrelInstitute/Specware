(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec
  import Parse_DTD_ElementDecl
  import Parse_DTD_AttlistDecl
  import Parse_DTD_EntityDecl    % includes parse_NotationDecl
  import Parse_PI

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          InternalDTD                                                                         %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: The XML document type declaration contains or points to markup declarations that
  %%   provide a grammar for a class of documents. This grammar is known as a document type
  %%   definition, or DTD. The document type declaration can point to an external subset (a special
  %%   kind of external entity) containing markup declarations, or can contain the markup declarations
  %%   directly in an internal subset, or can do both. The DTD for a document consists of both subsets
  %%   taken together.]
  %%
  %%  [Definition: A markup declaration is an element type declaration, an attribute-list declaration,
  %%   an entity declaration, or a notation declaration.]
  %%
  %%  These declarations may be contained in whole or in part within parameter entities, as
  %%  described in the well-formedness and validity constraints below.
  %%
  %%  The internal subset has the following physical form:
  %%
  %%  '<!DOCTYPE' S Name (S ExternalID)? S? DTD_Decls? '>'
  %%
  %%  It may contain the following atomic markup decls:
  %%
  %%   <!ELEMENT    ... >
  %%   <!ATTLIST    ... >
  %%   <!ENTITY     ... >
  %%   <!NOTATATION ... >
  %%
  %%  and/or the following decl separators:
  %%
  %%   <?   target value   ?>  -- PI           (i.e., program instruction)
  %%   <!--     ...       -->  -- Comment
  %%   % Name ;                -- PEReference  (parameter-entity reference)
  %%   space, tab, cr, lf      -- Whitespace
  %%
  %%
  %%  *[28]  doctypedecl    ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>'
  %%
  %%                                                            *[WFC: External Subset]
  %%                                                            *[VC:  Root Element Type]
  %%
  %% *[28a]  DeclSep        ::=  PEReference | S
  %%                                                            *[WFC: PE Between Declarations]
  %%
  %%
  %%  *[29]  markupdecl     ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment
  %%
  %%                                                            *[WFC: PEs in Internal Subset]
  %%                                                            *[VC:  Proper Declaration/PE Nesting]
  %%
  %%    ==>
  %%
  %%  [K11]  doctypedecl    ::=  '<!DOCTYPE' S Name (S ExternalID)? S? InternalDecls? '>'
  %%
  %%                                                             [KWFC: External Subset]
  %%                                                             [WFC:  PE Between Declarations]
  %%                                                             [WFC:  PEs in Internal Subset]
  %%                                                             [VC:  Root Element Type]
  %%                                                             [VC:  Proper Declaration/PE Nesting]
  %%
  %%  [K12]  InternalDecls  ::=  '[' InternalDecl* ']' S?
  %%  [K13]  InternalDecl   ::=  Decl
  %%                                                             [KWFC: Internal Decl]
  %%
  %%  [K14]  Decl           ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S | includeSect | ignoreSect
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K11]  doctypedecl    ::=  '<!DOCTYPE' S Name (S ExternalID)? S? InternalDecls? '>'
  %%
  %%                                                             [KWFC: External Subset]
  %%                                                             [WFC:  PE Between Declarations]
  %%                                                             [WFC:  PEs in Internal Subset]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: External Subset]                       [K11] *[28]  -- see parser/printer
  %%
  %%     The external subset, if any, must match the production for ExternalDTD.
  %%
  %%  The parser and printer enforce this restriction.
  %%
  %%  [WFC: PE Between Declarations]                [K11] *[28a] -- see parser/printer
  %%
  %%    The replacement text of a parameter entity reference in a DeclSep must match the production
  %%    extSubsetDecl.
  %%
  %%  The parser and printer enforce this restriction.
  %%
  %%  [WFC: PEs in Internal Subset]                 [K11] *[28] *[28a] *[29] -- no_pe_references_within_internal_markup?
  %%
  %%    In the internal DTD subset, parameter-entity references can occur only where markup
  %%    declarations can occur, not within markup declarations. (This does not apply to references
  %%    that occur in external parameter entities or to the external subset.)
  %% -------------------------------------------------------------------------------------------------

  def parse_InternalDTD (start : UChars) : Possible InternalDTD =
   case start of

     | 60 :: 33 :: 68 :: 79 :: 67 :: 84 :: 89 :: 80 :: 69 :: tail ->
       %% '<!DOCTYPE'
       {
	(w1,   tail) <- parse_WhiteSpace tail;
	(name, tail) <- parse_Name       tail;
	(wx,   tail) <- parse_WhiteSpace tail;
	case tail of

	  | 91 :: _ ->
	    %% '['
	    {
	     (decls, tail) <- parse_InternalDecls tail;
	     case tail of

	       | 62 :: tail ->
                 %% '>'
	         return (Some {w1          = w1,
			       name        = name,
			       w2          = None,
			       external_id = None,
			       w3          = wx,
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
		  return (Some {w1          = w1,
				name        = name,
				w2          = None,
				external_id = None,
				w3          = wx,
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
	     (external_id, tail) <- parse_ExternalID    tail;
	     (w3,          tail) <- parse_WhiteSpace    tail;
	     (decls,       tail) <- parse_InternalDecls tail;
	     case tail of

	       | 62 :: tail ->
                 %% '>'
	         return (Some {w1          = w1,
			       name        = name,
			       w2          = Some wx,
			       external_id = Some external_id,
			       w3          = w3,
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
		  return (Some {w1          = w1,
				name        = name,
				w2          = Some wx,
				external_id = Some external_id,
				w3          = w3,
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
     | _ -> return (None, start)

  %% -------------------------------------------------------------------------------------------------
  %%  [K12]  InternalDecls    ::=  '[' InternalDecl* ']' S?
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%  [K13]  InternalDecl     ::=  Decl
  %%                                                             [KWFC: Internal Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Internal Decl]                         [K14] *[28] *[28a] *[29] -- internal_decl?
  %%
  %%    InternalDecl ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S
  %% -------------------------------------------------------------------------------------------------

  %% -------------------------------------------------------------------------------------------------
  %%  [K14]  Decl             ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S | includeSect | ignoreSect
  %%
  %%  InternalDecl is a proper subset of Decl.
  %%  ExternalDecl equals Decl.
  %%
  %%  We unify them for parsing purposes to make handling of plausible
  %%  errors more robust.  (In particular, we anticipate that manual
  %%  movement of decls from the external subset to the internal subset
  %%  could introduce errors, as could mistakes made by document authors
  %%  confused by the similarity of the two subsets.)
  %% -------------------------------------------------------------------------------------------------

  def parse_InternalDecls (start : UChars) : Possible InternalDecls =
    %%
    %% We begin here with '[' pending in [K12], looking for:
    %%
    %%   '[' (DTD_Decl)* ']' S?
    %%
    case start of

      | 91 :: tail ->
        %% '['
        (let
            def probe (tail, rev_markups) =
	      case tail of

		| 93 :: tail ->
		  %% ']'
		  {
		   (w1, tail) <- parse_WhiteSpace tail;
		   return (Some {decls = reverse rev_markups,
				 w1    = w1},
			   tail)
		   }

                %% [29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment

		| 60 :: 33 :: 69 :: 76 :: 69 :: 77 :: 69 :: 78 :: 84 :: tail ->
                  %% '<!ELEMENT'
		  {
		   (decl, tail) <- parse_ElementDecl tail;
		   probe (tail, Element decl :: rev_markups)
		  }

		| 60 :: 33 :: 65 :: 84 :: 84 :: 76 :: 73 :: 83 :: 84 :: tail ->
                  %% '<!ATTLIST'
		  {
		   (decl, tail) <- parse_AttlistDecl tail;
		   probe (tail, Attributes decl :: rev_markups)
		  }

		| 60 :: 33 :: 69 :: 78 :: 84 :: 73 :: 84 :: 89 :: tail ->
                  %% '<!ENTITY'
		  {
		   (decl, tail) <- parse_EntityDecl (tail, false);
		   probe (tail, Entity decl :: rev_markups)
		  }

		| 60 :: 33 :: 78 :: 79 :: 84 :: 65 :: 84 :: 65 :: 84 :: 73 :: 79 :: 78 :: tail ->
                  %% '<!NOTATATION'
		  {
		   (decl, tail) <- parse_NotationDecl tail;
		   probe (tail, Notation decl :: rev_markups)
		  }

		| 60 :: 63 :: tail ->
                  %% '<?'
		  {
		   (decl, tail) <- parse_PI tail;
		   probe (tail, PI decl :: rev_markups)
		  }

		| 60 :: 45 :: 45 :: tail ->
                  %% '<--'
		  {
		   (comment, tail) <- parse_Comment tail;
		   probe (tail, Comment comment :: rev_markups)
		  }

                %% [28a] DeclSep      ::=  PEReference | S

		| 37 :: tail ->
                  %% '%'
		  {
		   (ref, tail) <- parse_PEReference tail;
		   probe (tail, PEReference ref :: rev_markups)
		  }

		| char :: _ ->
		  if white_char? char then
		    {
		     (w1, scout) <- parse_WhiteSpace tail;
		     probe (tail, WhiteSpace w1 :: rev_markups)
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
