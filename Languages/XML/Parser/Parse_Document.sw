
XML qualifying spec

  import Parse_Misc
  import Parse_XML_Decl
  import Parse_DTD
  import Parse_Element

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XML Document                                                                        %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [1]  document  ::=  prolog element Misc*
  %%
  %% [22]  prolog    ::=  XMLDecl? Misc* (doctypedecl  Misc*)?
  %%
  %% [27]  Misc      ::=  Comment | PI | S
  %%
  %%  [1] transforms as follows:
  %%
  %%       document  ::=  XMLDecl? Misc* (doctypedecl  Misc*)? element Misc*
  %%       document  ::=  XMLDecl? Misc*  doctypedecl? Misc*   element Misc*
  %%
  %%  so we can recast it as:
  %%
  %% [K1]  document  ::=  Misc*
  %%                                                             [WFC: at most one doctypedecl]
  %%                                                             [WFC: exactly one element]
  %%                                                             [WFC: doctypedecl preceeds eleement]
  %%
  %% [K2]  Misc      ::=  XMLDecl | Comment | PI | S | doctypedecl | element
  %% ----------------------------------------------------------------------------------------------------

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
		   (error ("WFC: XML decl is not the first form in an XML document", start, tail)));
		  (when (docs > 0)
		   (error ("WFC: XML decl follows Doctypedecl", start, tail)));
		  (when (elts > 0)
		   (error ("WFC: XML decl follows Element", start, tail)));
		  return (total + 1, xmls + 1, docs, elts)
		 }

	       | DTD        _ -> 
		 {
		  (when (elts > 0)
		   (error ("WFC: Doctypedecl (DTD) follows Element", start, tail)));
		  return (total + 1, xmls, docs + 1, elts)
		 }
	       | Element    _ -> 
		 return (total + 1, xmls, docs, elts + 1)
		 )
            (0, 0, 0, 0)
	    items);

     (when (xmls = 0)
      (error ("VC: No XML decl", start, tail)));

     (when (xmls > 1)
      (error ("WFC: Multiple XML decls", start, tail)));

     (when (docs > 1)
      (error ("WFC: Multiple Doctypedecl's (DTD's)", start, tail)));

     (when (elts = 0)
      (error ("WFC: No Element", start, tail)));

     (when (docs > 1)
      (error ("WFC: Multiple top-level Element's", start, tail)));

     let doc : Document = {items = items} in
     return (doc,
	     tail)
     }

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
	 (dtd, tail) <- parse_DocTypeDecl start;
	 return (DTD dtd,
		 tail)
	}

      %% Element
      | 60 (* '<' *) :: _ ->
	{
	 (possible_element, tail) <- parse_Element start;
	 case possible_element of
	   | Some element ->
	     return (Element element,
		     tail)
	   | _ ->
	     error ("Expected Whitespace, '<!--' (Comment), '<?' (PI), '<DOCTYPE' (DTD), or '<' (Element)",
		    start, tail)

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
	  error ("Expected Whitespace, '<!--' (Comment), '<?' (PI), '<DOCTYPE' (DTD), or '<' (Element)",
		 start, tail)

endspec
