(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import Parse_DTD_ElementDecl
  import Parse_DTD_AttlistDecl
  import Parse_DTD_EntityDecl    % includes parse_NotationDecl
  import Parse_PI
  import Parse_XMLDecl           % parse_TextDecl

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          ExternalDTD (External subset of Doc Type Decl)                                      %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [WFC: External Subset]                        *[28]
  %%
  %%  *The external subset, if any, must match the production for extSubset.
  %%
  %%  ==>
  %%
  %%  [KWFC: External Subset]                       [K11] *[28]
  %%
  %%   The external subset, if any, must match the production for ExternalDTD.
  %%
  %% -------------------------------------------------------------------------------------------------
  %%
  %%  For clarity, we rename "extSubset" to "ExternalDTD" :
  %%
  %%  *[30]  extSubset           ::=  TextDecl? extSubsetDecl
  %%  *[31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)*
  %%  *[61]  conditionalSect     ::=  includeSect | ignoreSect
  %%
  %%    ==>
  %%
  %%  [K15]  ExternalDTD         ::=  TextDecl? ExternalDecls
  %%                                                             [VC: Unique Element Type Declaration]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: One Notation Per Element Type]
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %%  [K16]  ExternalDecls       ::=  ExternalDecl*
  %%
  %%  [K17]  ExternalDecl        ::=  Decl
  %%
  %%  [Definition: Conditional sections are portions of the document type declaration external
  %%   subset which are included in, or excluded from, the logical structure of the DTD based on
  %%   the keyword which governs them.]
  %%
  %%   [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>'
  %%    ==>
  %%  [K18]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' ExternalDecls ']]>'
  %%
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %%
  %%  The following rule is infinitely ambiguous for no good reason, so simplify it.
  %%  [production [63] would accept any number of ignoreSectContents, which can be the null string.]
  %%   [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>'
  %%    ==>
  %%  [K19]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents ']]>'
  %%
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %%
  %%   [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %%
  %%   [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %%
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  renaming: extSubset => ExternalDTD
  %%  [K15]  ExternalDTD         ::=  TextDecl? ExternalDecls
  %% -------------------------------------------------------------------------------------------------

  %% DocTypeDecl is a logical structure containing the internal and external subsets.
  %% The internal subset is parsed as part of the character stream for the main document entity.
  %% It might contain an external id, which is a URI from which the external subset
  %% is parsed.  In particular, the external subset, if any, is parsed from a different
  %% character stream than the document entity.

  def parse_ExternalDTD (possible_internal_dtd : Option InternalDTD) : Env (Option ExternalDTD) =
    case possible_internal_dtd of
      | None -> return None
      | Some internal_dtd ->
        case internal_dtd.external_id of
          | None -> return None
	  | Some uri ->
	    {start <- get_uchars_from_uri uri;
	     parse_external_dtd start}

  def parse_external_dtd (start : UChars) : Env (Option ExternalDTD) =
    {
     (textdecl, tail) <- parse_TextDecl      start;
     (decls,    tail) <- parse_ExternalDecls tail;
     return (Some {textdecl = textdecl,
		   decls    = decls})
     }

  op get_uchars_from_uri : ExternalID -> Env UChars

  %% -------------------------------------------------------------------------------------------------
  %%  [K16]  ExternalDecls       ::=  ExternalDecl*
  %%  [K17]  ExternalDecl        ::=  Decl
  %% -------------------------------------------------------------------------------------------------

  def parse_ExternalDecls (start : UChars) : Required (List ExternalDecl) =
    let
        def probe (tail, rev_markups) =
	  case tail of

            | [] -> return (reverse rev_markups, [])

	    %%  [K14]  Decl           ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S | includeSect | ignoreSect

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

	    | 60 :: 33 :: 45 :: 45 :: tail ->
	      %% '<!--'
	      {
	       (comment, tail) <- parse_Comment tail;
	       probe (tail, Comment comment :: rev_markups)
	      }

	    | 37 :: tail ->
	      %% '%'
	      {
	       (ref, tail) <- parse_PEReference tail;
	       probe (tail, PEReference ref :: rev_markups)
	      }

	    | 60 :: 33 :: 91 :: tail ->
	      %% "<!["
	      {
	       (w1, tail) <- parse_WhiteSpace tail;
	       case tail of
		 | 73 :: 78 :: 67 :: 76 :: 85 :: 68 :: 69 :: tail ->
		   %% "INCLUDE"
		   {
		    (include, tail) <- parse_IncludeSect (tail, w1);
		    probe (tail, Include include :: rev_markups)
		    }
		 | 73 :: 71 :: 78 :: 79 :: 82 :: 69 :: tail ->
		   %% "IGNORE"
		   {
		    (ignore, tail) <- parse_IgnoreSect (tail, w1);
		    probe (tail, Ignore ignore :: rev_markups)
		    }
	         | _ ->
	           hard_error {kind        = Syntax,
			       requirement = "In the external DTD subset, '<![' indicates an include or ignore decl",
			       start       = start,
			       tail        = tail,
			       peek        = 10,
			       we_expected = [("'<![' S 'INCLUDE'",    "include decl"),
					      ("'<![' S 'IGNORE'",     "ignore  decl")],
			       but         = "something other than INCLUDE or IGNORE was seen",
			       so_we       = "fail immediately"}
		    }

	    | char :: _ ->
	      if white_char? char then
		{
		 (w1, tail) <- parse_WhiteSpace tail;
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
					   ("'<!--'",                 "comment"),
					   ("'%'",                    "PE Reference"),
					   ("'<![' S 'INCLUDE'",      "include decl"),
					   ("'<![' S 'IGNORE'",       "ignore  decl"),
					   ("( #9 | #A | #D | #20 )", "whitespace"),
					   ("']'",                    "end of markups in DTD")],
			    but         = (describe_char char) ^ " was seen instead",
			    so_we       = "fail immediately"}

(*
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
					   ("'<![' S 'INCLUDE'",      "include decl"),
					   ("'<![' S 'IGNORE'",       "ignore  decl"),
					   ("( #9 | #A | #D | #20 )", "whitespace"),
					   ("']'",                    "end of markups in DTD")],
			    but         = "EOF occurred first",
			    so_we       = "fail immediately"}
*)
    in
      probe (start, [])


  %% -------------------------------------------------------------------------------------------------
  %%  [K18]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' ExternalDecls ']]>'
  %% -------------------------------------------------------------------------------------------------

  def parse_IncludeSect (start : UChars, w1 : WhiteSpace) : Required IncludeSect =
    %% We arrrive here just past 'INCLUDE'
    {
     (w2,    tail) <- parse_WhiteSpace start;
     case tail of
       | 91 :: tail ->
         %% '['
	 {
	  (decls, tail) <- parse_ExternalDecls tail;
	  case tail of
	    | 93 :: 93 :: 62 :: tail ->
	      %% ']]>'
	      return ({w1    = w1,
		       w2    = w2,
		       decls = decls},
		      tail)
	    | _ ->
	      hard_error {kind        = Syntax,
			  requirement = "includeSect  ::=  '<![' S? 'INCLUDE' S? '[' ExternalDecls ']]>'",
			  start       = start,
			  tail        = [],
			  peek        = 10,
			  we_expected = [("']]>'",            "termination of include decl")],
			  but         = "we saw something else",
			  so_we       = "fail immediately"}
	     }
       | _ ->
         hard_error {kind        = EOF,
		     requirement = "includeSect  ::=  '<![' S? 'INCLUDE' S? '[' ExternalDecls ']]>'",
		     start       = start,
		     tail        = [],
		     peek        = 10,
		     we_expected = [("'['",            "initiation of decls")],
		     but         = "we saw something else",
		     so_we       = "fail immediately"}
	}

  %% -------------------------------------------------------------------------------------------------
  %%  [K19]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents ']]>'
  %% -------------------------------------------------------------------------------------------------

  def parse_IgnoreSect (start : UChars, w1 : WhiteSpace) : Required IgnoreSect =
    %% We arrrive here just past 'IGNORE'
    {
     (w2, tail) <- parse_WhiteSpace start;
     case tail of
       | 91 :: tail ->
         %% '['
	 {
	  (contents : IgnoreSectContents, tail) <- parse_IgnoreSectContents tail;
	  return ({w1       = w1,
		   w2       = w2,
		   contents = contents},
		  tail)
	  }
       | _ ->
         hard_error {kind        = EOF,
		     requirement = "ignoreSect  ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>'",
		     start       = start,
		     tail        = [],
		     peek        = 10,
		     we_expected = [("'['", "initiation of ignored stuff")],
		     but         = "we saw something else",
		     so_we       = "fail immediately"}
	}

  %% -------------------------------------------------------------------------------------------------
  %%   [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %%   [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% -------------------------------------------------------------------------------------------------

  def parse_IgnoreSectContents (start : UChars) : Required IgnoreSectContents =
    let
        def parse_ignore (tail, rev_ignore) =
	  case tail of
	    | 93 :: 93 :: 62 :: _ ->
	      %% "]]>"
              return (reverse rev_ignore, tail)
	    | 60 :: 33 :: 91 :: _ ->
	      %% "<!["
              return (reverse rev_ignore, tail)
	    | char :: tail ->
	      parse_ignore (tail, char::rev_ignore)
	    | _ ->
	      hard_error {kind        = EOF,
			  requirement = "ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*",
			  start       = start,
			  tail        = [],
			  peek        = 10,
			  we_expected = [("']]>'",            "termination of ignoreSectContents"),
					 ("'<!['",            "new level of ignoreSectContents"),
					 ("Char",             "continutation of ignored text")],
			  but         = "EOF occurred",
			  so_we       = "fail immediately"}
        def probe (tail, prefix, rev_contents) =
	  {
	   (i_s_c,  tail) <- parse_IgnoreSectContents tail;
	   (ignore, tail) <- parse_ignore             (tail, []);
	   let rev_contents = Cons ((i_s_c, ignore), rev_contents) in
	   case tail of
	     | 93 :: 93 :: 62 :: tail ->
	       %% "]]>"
	       return ({prefix   = prefix,
			contents = reverse rev_contents},
		       tail)
	     | 60 :: 33 :: 91 :: tail ->
	       %% "<!["
	       probe (tail, prefix, rev_contents)

	      }
    in
      {
       (prefix, tail) <- parse_ignore (start, []);
       case tail of
	 | 93 :: 93 :: 62 :: tail ->
	   %% "]]>"
	   return ({prefix   = prefix,
		    contents = []},
		   tail)
	 | 60 :: 33 :: 91 :: tail ->
	   %% "<!["
	   probe (tail, prefix, [])
	  }

endspec
