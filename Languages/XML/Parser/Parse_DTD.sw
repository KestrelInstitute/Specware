
XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Data_Type_Document                                                                  %%%
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
  %% [28]  doctypedecl     ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>' 
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%
  %% [28a]  DeclSep        ::=  PEReference | S    
  %%                                                             [WFC: PE Between Declarations]
  %%
  %% [29]  markupdecl      ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 
  %%
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %%                                                             [WFC: PEs in Internal Subset]
  %% -------------------------------------------------------------------------------------------------
  %% [45]  elementdecl     ::=  '<!ELEMENT' S Name S contentspec S? '>' 
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %% [46]  contentspec     ::=  'EMPTY' | 'ANY' | Mixed | children 
  %%
  %% [47]  children        ::=  (choice | seq) ('?' | '*' | '+')? 
  %%
  %% [48]  cp              ::=  (Name | choice | seq) ('?' | '*' | '+')? 
  %%
  %% [49]  choice          ::=  '(' S? cp ( S? '|' S? cp )+ S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%
  %% [50]  seq             ::=  '(' S? cp ( S? ',' S? cp )* S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %% [51]  Mixed           ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%                                                             [VC: No Duplicate Types]
  %% ------------------------------------------------------------------------------------------------
  %% [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
  %%
  %% [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %%
  %% [54]  AttType         ::=  StringType | TokenizedType | EnumeratedType 
  %%
  %% [55]  StringType      ::=  'CDATA'
  %%
  %% [56]  TokenizedType   ::=    'ID'                           [VC: ID]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: ID Attribute Default]
  %%                            | 'IDREF'                        [VC: IDREF]
  %%                            | 'IDREFS'                       [VC: IDREF]
  %%                            | 'ENTITY'                       [VC: Entity Name]
  %%                            | 'ENTITIES'                     [VC: Entity Name]
  %%                            | 'NMTOKEN'                      [VC: Name Token]
  %%                            | 'NMTOKENS'                     [VC: Name Token]
  %%
  %% [57]  EnumeratedType  ::=  NotationType | Enumeration 
  %%
  %% [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')' 
  %%
  %%                                                             [VC: Notation Attributes] 
  %%                                                             [VC: One Notation Per Element Type] 
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %% [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')' 
  %%
  %%                                                             [VC: Enumeration]
  %%
  %% [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue) 
  %%
  %%                                                             [VC:  Required Attribute] 
  %%                                                             [VC:  Attribute Default Legal]
  %%                                                             [WFC: No < in Attribute Values]
  %%                                                             [VC:  Fixed Attribute Default]
  %% ------------------------------------------------------------------------------------------------
  %% [70]  EntityDecl      ::=  GEDecl | PEDecl
  %%
  %% [71]  GEDecl          ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %%
  %% [72]  PEDecl          ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %%
  %% [73]  EntityDef       ::=  EntityValue | (ExternalID NDataDecl?)
  %%
  %% [74]  PEDef           ::=  EntityValue | ExternalID
  %%
  %% [75]  ExternalID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
  %%
  %% [76]  NDataDecl       ::=  S 'NDATA' S Name 
  %%
  %%                                                             [VC: Notation Declared]
  %% ------------------------------------------------------------------------------------------------
  %% [82]  NotationDecl    ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>' 
  %%
  %%                                                             [VC: Unique Notation Name]
  %%
  %% [83]  PublicID        ::=  'PUBLIC' S PubidLiteral 
  %% ----------------------------------------------------------------------------------------------------

  def parse_DocTypeDecl (start : UChars) : Required DocTypeDecl =
   %% [28]  doctypedecl     ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>' 
   %% assumes we're just past '<!DOCTYPE'
   {
    (w1,          tail) <- parse_WhiteSpace start;
    (name,        tail) <- parse_Name       tail;
    (external_id, tail) <- parse_ExternalID tail;
    (w3,          tail) <- parse_WhiteSpace tail;
    (markups,     tail) <- parse_markups    tail;
    case tail of
      | 62 (* '>' *) :: tail ->
        return ({w1          = w1,
		 name        = name,
		 external_id = external_id,
		 w3          = w3,
		 markups     = markups},
		tail)
      | _ ->
	error ("DTD doesn't end with '>'", start, nthTail (tail, 10))
       }

  def parse_ExternalID (start : UChars) : Possible (WhiteSpace * ExternalID) =
    {
     (w1, tail) <- parse_WhiteSpace start;
     if null w1 then
       return (None, start)
     else
       %% [75]  ExternalID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral 
       case tail of 
	 | 83 :: 89 :: 83 :: 84 :: 69 :: 77 (* 'SYSTEM' *) :: tail ->
	   {
	    (w2,     tail) <- parse_WhiteSpace tail;
	    (syslit, tail) <- parse_SystemLiteral tail;
	    return (Some (w1, System (w2, syslit)),
		    tail)
	    }

         | 80 :: 85 :: 66 :: 76 :: 73 :: 67 (* 'PUBLIC' *) :: tail ->
	   {
	    (w2,     tail) <- parse_WhiteSpace    tail;
	    (publit, tail) <- parse_PubidLiteral  tail;
	    (w3,     tail) <- parse_WhiteSpace    tail;
	    (syslit, tail) <- parse_SystemLiteral tail;
	    return (Some (w1, Public (w2, publit, w3, syslit)),
		    tail)
	    }
	 | _ ->
	   return (None, start)
	  }	
	 
  op parse_markups    : UChars -> Possible (List (| Decl MarkupDecl | Sep DeclSep) * 
					    WhiteSpace)

  op parse_SystemLiteral : UChars -> Required SystemLiteral

  op parse_PubidLiteral : UChars -> Required PubidLiteral

  op parse_MarkupDecl : UChars -> Possible MarkupDecl

  op parse_ElementDecl : UChars -> Possible ElementDecl

  op parse_ContentSpec : UChars -> Required ContentSpec

  op parse_Mixed : UChars -> Possible Mixed

  op parse_Children : UChars -> Possible Children

  op parse_Choice : UChars -> Possible Choice

  op parse_CP : UChars -> Required CP

  op parse_Seq : UChars -> Required Seq

  op parse_AttlistDecl : UChars -> Possible AttlistDecl

  op parse_AttDef : UChars -> Possible AttDef

  op parse_AttType : UChars -> Possible AttType

  op parse_TokenizedType : UChars -> Possible TokenizedType

  op parse_EnumeratedType : UChars -> Possible EnumeratedType

  op parse_NotationType : UChars -> Possible NotationType

  op parse_Enumeration : UChars -> Possible Enumeration

  op parse_EntityDecl : UChars -> Possible EntityDecl

  op parse_GEDecl : UChars -> Possible GEDecl

  op parse_EntityDef : UChars -> Required EntityDef

  op parse_NDataDecl : UChars -> Possible NDataDecl

  op parse_PEDecl : UChars -> Possible PEDecl

  op parse_PEDef : UChars -> Possible PEDef

  op parse_NotationDecl : UChars -> Possible NotationDecl

  op parse_PublicID : UChars -> Possible PublicID

  op parse_DefaultDecl : UChars -> Possible DefaultDecl

  op parse_DeclSep : UChars -> Possible DeclSep


endspec