
XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Data_Type_Document -- NotationDecl                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [82]  NotationDecl  ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>' 
  %%
  %%                                                             [VC: Unique Notation Name]
  %%
  %% [75]  ExternalID    ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
  %%  ==>
  %% [K14] ExternalID    ::=  GenericID
  %% 
  %%                                                             [KC: At Least SYSTEM]
  %% 
  %% [83]  PublicID      ::=  'PUBLIC' S PubidLiteral 
  %%  ==>
  %% [K15] PublicID      ::=  GenericID
  %% 
  %%                                                             [KC: Just PUBLIC]
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
  %% [75]  ExternalID  ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
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
	 
  def parse_SystemLiteral (start : UChars) : Required SystemLiteral =
    parse_QuotedText start

  def parse_PubidLiteral (start : UChars) : Required PubidLiteral =
    parse_QuotedText start

endspec