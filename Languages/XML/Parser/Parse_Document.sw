
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
		   (error (WFC {description = "XML decl is not the first form in an XML document"})));
		  (when (docs > 0)
		   (error (WFC {description = "XML decl follows Doctypedecl"})));
		  (when (elts > 0)
		   (error (WFC {description = "XML decl follows Element"})));
		  return (total + 1, xmls + 1, docs, elts)
		 }

	       | DTD        _ -> 
		 {
		  (when (elts > 0)
		   (error (WFC {description = "Doctypedecl (DTD) follows Element"})));
		  return (total + 1, xmls, docs + 1, elts)
		 }
	       | Element    _ -> 
		 return (total + 1, xmls, docs, elts + 1)
		 )
            (0, 0, 0, 0)
	    items);

     (when (xmls = 0)
      (error (VC {description = "No 'xml' decl"})));

     (when (xmls > 1)
      (error (WFC {description = "Multiple 'xml' decls"})));

     (when (docs > 1)
      (error (WFC {description = "Multiple DTD's (doctypedecl's)"})));

     (when (elts = 0)
      (error (WFC {description = "No Element in document"})));

     (when (docs > 1)
      (error (WFC {description = "Multiple top-level Element's"})));

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
	 (possible_element, tail) <- parse_Element start;
	 case possible_element of
	   | Some element ->
	     return (Element element,
		     tail)
	   | _ ->
	     hard_error (Surprise {context  = "After a '<' while looking for top-level doc-item",
				   expected = [("'<?xml'",     "initial xml decl"),
					       ("'<?'",        "PI"),
					       ("'<!--'",      "Comment"),
					       ("'<!DOCTYPE'", "DTD"), 
					       ("'<'",         "Element")],
				   action   = "immediate failure",
				   start    = start, 
				   tail     = scout,
				   peek     = 10})
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
	  hard_error (Surprise {context  = "Looking for top-level doc-item",
				expected = [("'<?xml'",           "initial xml decl"),
					    ("'<?'",              "PI"),
					    ("'<!--'",            "Comment"),
					    ("#x9 #xA #xD #x20",  "WhiteSpace"),
					    ("'<!DOCTYPE'",       "DTD"), 
					    ("'<'",               "Element")],
				action   = "immediate failure",
				start    = start, 
				tail     = tail,
				peek     = 10})
      | _ ->
	  hard_error (EOF {context = "Parsing top-level document items",
			   start   = start})

endspec
