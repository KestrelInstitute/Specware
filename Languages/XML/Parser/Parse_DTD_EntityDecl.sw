XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD EntityDecl                                                                      %%%
  %%%          DTD NotationDecl                                                                    %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%  [70]  EntityDecl     ::=  GEDecl | PEDecl
  %%
  %%  [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %%
  %%  [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %%
  %%  [73]  EntityDef      ::=  EntityValue | (ExternalID NDataDecl?)
  %%
  %%  [74]  PEDef          ::=  EntityValue | ExternalID
  %%
  %%  [76]  NDataDecl      ::=  S 'NDATA' S Name 
  %%
  %%                                                             [VC: Notation Declared]
  %%
  %% ------------------------------------------------------------------------------------------------
  %%
  %%  [82]  NotationDecl   ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>' 
  %%
  %%                                                             [VC: Unique Notation Name]
  %%
  %% ------------------------------------------------------------------------------------------------
  %%
  %% *[75]  ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
  %%   ==>
  %% [K16]  ExternalID     ::=  GenericID
  %%
  %%                                                             [KC: At Least SYSTEM]
  %%
  %% *[83]  PublicID       ::=  'PUBLIC' S PubidLiteral 
  %%   ==>
  %% [K17]  PublicID       ::=  GenericID
  %%
  %%                                                             [KC: Just PUBLIC]
  %%
  %% [K18]  GenericID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral (S SystemLiteral)?
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%
  %%  [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %%  [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %%
  def parse_EntityDecl (start : UChars) : Required EntityDecl =
    %% We begin here just past the '<!ENTITY' in rules [71] and [72], looking for
    %% one of the following:
    %%  S       Name S EntityDef S? '>'
    %%  S '%' S Name S PEDef     S? '>'
    {
     (w1, tail) <- parse_WhiteSpace start;
     case tail of
       | 37 (* '%' *) :: tail ->
         %%  PEDecl
         {
	  (w2,    tail) <- parse_WhiteSpace tail;
	  (name,  tail) <- parse_Name       tail;
	  (w3,    tail) <- parse_WhiteSpace tail;
	  (pedef, tail) <- parse_PEDef      tail;
	  (w4,    tail) <- parse_WhiteSpace tail;
	  case tail of
	    | 62 (* '>' *) :: tail ->
	      return (PE {w1    = w1,
			  w2    = w2,
			  name  = name,
			  w3    = w3,
			  pedef = pedef,
			  w4    = w4},
		      tail)
	    | _ ->
	      error ("Looking for '>' at end of PEDecl in DTD",
		     start, nthTail (tail, 10))
	      }
       | _ ->
	 %% GEDecl 
	 {
	  (name, tail) <- parse_Name       tail;
	  (w2,   tail) <- parse_WhiteSpace tail;
	  (edef, tail) <- parse_EntityDef  tail;
	  (w3,   tail) <- parse_WhiteSpace tail;
	  case tail of
	    | 62 (* '>' *) :: tail ->
	      return (GE {w1   = w1,
			  name = name,
			  w2   = w2,
			  edef = edef,
			  w3   = w3},
		      tail)
	    | _ ->
	      error ("Looking for '>' at end of GEDecl in DTD",
		     start, nthTail (tail, 10))
	      }}

  %%
  %%  [73]  EntityDef     ::=  EntityValue | (ExternalID NDataDecl?)
  %%   [9]  EntityValue   ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %% *[75]  ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
  %%
  def parse_EntityDef (start : UChars) : Required EntityDef =
    case start of
      | 34 (* double-quote *) :: tail ->
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }
      | 39 (* apostrophe *) :: tail ->
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }
      | _ ->
	{
	 (ext_id, tail) <- parse_GenericID start;
	 (ndata,  tail) <- parse_NDataDecl tail;
	 return (External (ext_id, ndata),
		tail)
	}

  %%
  %%  [74]  PEDef          ::=  EntityValue | ExternalID
  %%
  def parse_PEDef (start : UChars) : Required PEDef =
    case start of
      | 34 (* double-quote *) :: tail ->
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }
      | 39 (* apostrophe *) :: tail ->
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }
      | _ ->
	{
	 (ext_id, tail) <- parse_GenericID start;
	 return (External ext_id, tail)
	 }

  %%
  %%  [76]  NDataDecl      ::=  S 'NDATA' S Name 
  %%
  def parse_NDataDecl (start : UChars) : Possible NDataDecl =
    {
     (w1, tail) <- parse_WhiteSpace start;
     case tail of
       | 78 :: 68 :: 65 :: 84 :: 65 (* 'NDATA' *) :: tail -> 
         {
	  (w2,   tail) <- parse_WhiteSpace tail;
	  (name, tail) <- parse_Name       tail;
	  return (Some {w1   = w1,
			w2   = w2,
			name = name},
		  tail)
	  }
       | _ -> return (None, start)
	}

  %%
  %% [82]  NotationDecl  ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>' 
  %%
  def parse_NotationDecl (start : UChars) : Required NotationDecl =
    %% 
    %% We begin just past '<!NOTATION' in rule 82, looking for:
    %% 
    %%  S Name S (ExternalID | PublicID) S? '>' 
    %% 
    {
     (w1,   tail) <- parse_WhiteSpace start;
     (name, tail) <- parse_Name       tail;
     (w2,   tail) <- parse_WhiteSpace tail;
     (id,   tail) <- parse_GenericID  tail;  % (ExternalID | PublicID)
     (w3,   tail) <- parse_WhiteSpace tail;
     case tail of 
       | 62 (* '>' *) :: tail ->
         return ({w1   = w1,
		  name = name,
		  w2   = w2,
		  id   = id,
		  w3   = w3},
		 tail)
       | _ ->
	 error ("Expected '<!NOTATION' to close with '>'",
		start, tail)
	}

  %%
  %% [K16] GenericID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral (S SystemLiteral)?
  %%
  def parse_GenericID (start : UChars) : Required GenericID =
    case start of 
      | 83 :: 89 :: 83 :: 84 :: 69 :: 77 (* 'SYSTEM' *) :: tail ->
        {
	 (w2,     tail) <- parse_WhiteSpace tail;
	 (syslit, tail) <- parse_SystemLiteral tail;
	 return ({w1     = null_whitespace,
		  public = None,
		  w2     = w2,
		  system = Some syslit},
		 tail)
	}

      | 80 :: 85 :: 66 :: 76 :: 73 :: 67 (* 'PUBLIC' *) :: tail ->
	{
	 (w1,     tail) <- parse_WhiteSpace    tail;
	 (publit, tail) <- parse_PubidLiteral  tail;
	 (w2,     scout) <- parse_WhiteSpace    tail;
	 case scout of
	   | 62 (* '>' *) :: tail ->
	     return ({w1     = w1,
		      public = Some publit,
		      w2     = null_whitespace,
		      system = None},
		     scout)
	   | _ ->
	     {
	      (syslit, tail) <- parse_SystemLiteral tail;
	      return ({w1     = w1,
		       public = Some publit,
		       w2     = w2,
		       system = Some syslit},
		      tail)
	      }}
      | _ ->
	error ("Expected 'SYSTEM' or 'PUBLIC' in DTD", start, nthTail(start, 10))
	 
endspec
