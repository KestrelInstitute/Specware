
XML qualifying spec

  import Parse_XMLDecl
  import Parse_DTD
  import Parse_Element

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Document                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  *[1]  document  ::=  prolog element Misc*
  %%
  %% *[22]  prolog    ::=  XMLDecl? Misc* (doctypedecl  Misc*)?
  %%
  %% *[27]  Misc      ::=  Comment | PI | S
  %%
  %% -------------------------------------------------------------------------------------------------
  %%
  %%   [1] transforms as follows:
  %%
  %%       document  ::=  XMLDecl? Misc* (doctypedecl  Misc*)? element Misc*
  %%       document  ::=  XMLDecl? Misc*  doctypedecl? Misc*   element Misc*
  %%
  %%  so we can recast [1] [22] [27] as:
  %%
  %%  [K1]  document  ::=  DocItems
  %%
  %%                                                             [KC: Well-Formed Doc]
  %%                                                             [KC: Valid Doc]  
  %%
  %%  [K2]  DocItems  ::=  DocItem*
  %%
  %%  [K3]  DocItem   ::=  XMLDecl | Comment | PI | S | doctypedecl | element
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K1]  document  ::=  DocItems
  %%                                                             [KC: Well-Formed Doc]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Document (start  : UChars) : Required Document =
    {
     (items, tail) <- parse_DocItems start;
     (total, xmls, docs, elts) <-
     (foldM (fn (total, xmls, docs, elts) -> fn item ->
	     case item of
	       | Comment    _ -> return (total + 1, xmls, docs, elts)
	       | PI         _ -> return (total + 1, xmls, docs, elts)
	       | WhiteSpace _ -> return (total + 1, xmls, docs, elts)
	       | XMLDecl    _ -> 
		 {
		  (when (total > 0)
		   (error {kind        = WFC,
			   requirement = "Any xml header decl should be right at the start of the document.",
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   but         = "an xml header decl is not the first form in the XML document",
			   so_we       = "proceed anyway"}));
		  (when (docs > 0)
		   (error {kind        = WFC,
			   requirement = "Any xml header decl should be right at the start of the document.",
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   but         = "an xml header decl follows the DTD",
			   so_we       = "proceed anyway"}));
		  (when (elts > 0)
		   (error {kind        = WFC,
			   requirement = "Any xml header decl should be right at the start of the document.",
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   but         = "an xml header decl follows the top-level element",
			   so_we       = "proceed anyway"}));
		  return (total + 1, xmls + 1, docs, elts)
		 }

	       | DTD        _ -> 
		 {
		  (when (elts > 0)
		   (error {kind        = WFC,
			   requirement = "Any DTD decl must be second (after the xml header decl).",
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   but         = "the DTD decl follows the top-level element",
			   so_we       = "proceed anyway"}));
		  return (total + 1, xmls, docs + 1, elts)
		 }
	       | Element    _ -> 
		 return (total + 1, xmls, docs, elts + 1)
		 )
            (0, 0, 0, 0)
	    items);

     (when (xmls = 0)
      (error {kind        = VC,
	      requirement = "Each XML document should begin with an xml header decl.",
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      but         = "there is no xml header decl",
	      so_we       = "proceed anyway"}));

     (when (xmls > 1)
      (error {kind        = VC,
	      requirement = "Each XML document should begin with an xml header decl.",
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      but         = "there are multiple xml header decls",
	      so_we       = "proceed anyway"}));

     (when (docs > 1)
      (error {kind        = WFC,
	      requirement = "Each XML document may have at most one DTD.",
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      but         = "there are multiple DTD's (doctypedecl's)",
	      so_we       = "proceed anyway"}));

     (when (elts = 0)
      (error {kind        = WFC,
	      requirement = "Each XML document must have exactly one top-level element.",
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      but         = "there is no top-level element in the document",
	      so_we       = "proceed anyway"}));

     (when (elts > 1)
      (error {kind        = WFC,
	      requirement = "Each XML document must have exactly one top-level element.",
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      we_expected = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      but         = "there are multiple top-level elements",
	      so_we       = "proceed anyway"}));

     let doc : Document = {items = items} in
     return (doc,
	     tail)
     }

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K2]  DocItems  ::=  DocItem*
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_DocItems (start : UChars) : Required DocItems =
    let 
       def probe (tail, rev_items) =
	 case tail of
	   | [] -> return (rev rev_items, [])
	   | _ ->
	     {
	      (item, tail) <- parse_DocItem tail;
	      (probe (tail, cons (item, rev_items)))
	      }
    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [K3]  DocItem   ::=  XMLDecl | Comment | PI | S | doctypedecl | element
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_DocItem (start : UChars) : Required DocItem =
    %% Comment | PI | S | doctypedecl | element
    case start of

      %% Comment
      | 60 :: 33 :: 45 :: 45 (* '<!--' *) :: tail ->
        {
	 (comment, tail) <- parse_Comment tail;
	 return (Comment comment,
		 tail)
	}

      %% XML/PI
      | 60 :: 63 (* '<?' *) :: tail -> 
        (case tail of

	  %% XML
	  | 120 :: 109 :: 108 (* 'xml' *) :: _ ->
	    {
	     (xml, tail) <- parse_XMLDecl start;
	     return (XMLDecl xml,
		     tail)
	    }

	  %% PI
	  | _ ->
	    {
	     (pi, tail) <- parse_PI start;
	     return (PI pi, 
		     tail)
	    })

      %% DTD
      | 60 :: 33 :: 68 :: 79 :: 67 :: 84 :: 89 :: 80 :: 69 (* '<!DOCTYPE' *) :: tail ->
	{
	 (dtd, tail) <- parse_DocTypeDecl tail;
	 return (DTD dtd,
		 tail)
	}

      %% Element
      | 60 (* '<' *) :: scout ->
	{
	 (possible_element, tail) <- parse_Element (start, []);
	 case possible_element of
	   | Some element ->
	     return (Element element,
		     tail)
	   | _ ->
	     hard_error {kind        = Syntax,
			 requirement = "There should be one top-level element in an XML Document.",
			 start       = start, 
			 tail        = scout,
			 peek        = 10,
			 we_expected = [("'<?xml'",     "initial xml decl"),
					("'<?'",        "PI"),
					("'<!--'",      "Comment"),
					("'<!DOCTYPE'", "DTD"), 
					("'<'",         "Element")],
			 but         = "there are no top-level elements",
			 so_we       = "fail immediately"}
	    }

      %% Whitespace
      | char :: tail ->
	if white_char? char then
	  {
	   (whitespace, tail) <- parse_WhiteSpace start;
	   return (WhiteSpace whitespace,
		   tail)
	   }
	else
	  hard_error {kind        = Syntax,
		      requirement = "Each top-level item in an XML Document should be one of the options below.",
		      start       = start, 
		      tail        = tail,
		      peek        = 10,
		      we_expected = [("'<?xml'",           "initial xml decl"),
				     ("'<?'",              "PI"),
				     ("'<!--'",            "Comment"),
				     ("#x9 #xA #xD #x20",  "WhiteSpace"),
				     ("'<!DOCTYPE'",       "DTD"), 
				     ("'<'",               "Element")],
		      but         = (describe_char char) ^ " was seen instead",
		      so_we       = "fail immediately"}
      | _ ->
	  hard_error {kind        = EOF,
		      requirement = "Each top-level item in an XML Document should be one of the options below.",
		      start       = start,
		      tail        = [],
		      peek        = 0,
		      we_expected = [("'<?xml'",           "initial xml decl"),
				     ("'<?'",              "PI"),
				     ("'<!--'",            "Comment"),
				     ("#x9 #xA #xD #x20",  "WhiteSpace"),
				     ("'<!DOCTYPE'",       "DTD"), 
				     ("'<'",               "Element")],
		      but         = "EOF occurred first",
		      so_we       = "fail immediately"}

endspec
