
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
  %%                                                             [KC: Well-Formed Doc]
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
			   problem     = "An XML decl is not the first form in an XML document.",
			   expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   action      = "Proceed anyway"}));
		  (when (docs > 0)
		   (error {kind        = WFC,
			   requirement = "Any xml header decl should be right at the start of the document.",
			   problem     = "An xml header decl follows DTD.",
			   expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   action      = "Proceed anyway"}));
		  (when (elts > 0)
		   (error {kind        = WFC,
			   requirement = "Any xml header decl should be right at the start of the document.",
			   problem     = "An xml header decl follows Element",
			   expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   action      = "Proceed anyway"}));
		  return (total + 1, xmls + 1, docs, elts)
		 }

	       | DTD        _ -> 
		 {
		  (when (elts > 0)
		   (error {kind        = WFC,
			   requirement = "Any DTD decl must be second (after xml header decl)",
			   problem     = "DTD decl follows Element",
			   expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
			   start       = start,
			   tail        = tail,
			   peek        = 0,
			   action      = "Proceed anyway"}));
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
	      problem     = "No 'xml' decl",
	      expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      action      = "Proceed anyway"}));

     (when (xmls > 1)
      (error {kind        = VC,
	      requirement = "Each XML document should begin with an xml header decl.",
	      problem     = "Multiple 'xml' decls",
	      expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      action      = "Proceed anyway"}));

     (when (docs > 1)
      (error {kind        = WFC,
	      requirement = "Each XML document may have at most one DTD.",
	      problem     = "Multiple DTD's (doctypedecl's)",
	      expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      action      = "Proceed anyway"}));

     (when (elts = 0)
      (error {kind        = WFC,
	      requirement = "Each XML document must have exactly one top-level element.",
	      problem     = "No element in document.",
	      expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      action      = "Proceed anyway"}));

     (when (elts > 1)
      (error {kind        = WFC,
	      requirement = "Each XML document must have exactly one top-level element.",
	      problem     = "Multiple top-level Element's.",
	      expected    = [("xml dtd? element", "xml decl first, optional DTD second, main element last")],
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      action      = "Proceed anyway"}));

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
			 problem     = "No Element was found.",
			 expected    = [("'<?xml'",     "initial xml decl"),
					("'<?'",        "PI"),
					("'<!--'",      "Comment"),
					("'<!DOCTYPE'", "DTD"), 
					("'<'",         "Element")],
			 start       = start, 
			 tail        = scout,
			 peek        = 10,
			 action      = "immediate failure"}
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
		      problem     = (describe_char char) ^ " was unexpected.",
		      expected    = [("'<?xml'",           "initial xml decl"),
				     ("'<?'",              "PI"),
				     ("'<!--'",            "Comment"),
				     ("#x9 #xA #xD #x20",  "WhiteSpace"),
				     ("'<!DOCTYPE'",       "DTD"), 
				     ("'<'",               "Element")],
		      start       = start, 
		      tail        = tail,
		      peek        = 10,
		      action      = "immediate failure"}
      | _ ->
	  hard_error {kind        = EOF,
		      requirement = "Each top-level item in an XML Document should be one of the options below.",
		      problem     = "EOF occurred first.",
		      expected    = [("'<?xml'",           "initial xml decl"),
				     ("'<?'",              "PI"),
				     ("'<!--'",            "Comment"),
				     ("#x9 #xA #xD #x20",  "WhiteSpace"),
				     ("'<!DOCTYPE'",       "DTD"), 
				     ("'<'",               "Element")],
		      start       = start,
		      tail        = [],
		      peek        = 0,
		      action      = "immediate failure"}

endspec
