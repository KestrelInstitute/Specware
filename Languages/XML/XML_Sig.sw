XML qualifying spec

  import Utilities/XML_Base
  import Utilities/XML_Unicode


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          W3 Specification of XML                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%
  %%% Grammar conventions:
  %%%
  %%%   The grammar used here is based on the grammar specified by the rules [1]-[85], 
  %%%   (but note there are no rules 33-38 or 79), found at 
  %%%   http://www.w3.org/TR/REC-xml#sec-documents
  %%%   and carefully quoted here (including their associated conditions tagged as 
  %%%   one of:
  %%%
  %%%     WFC : Well-formedness constraint
  %%%     VC  : Validity constraint
  %%%
  %%%   An explanation of each WFC/VC is included at the end of this file.
  %%%
  %%%   A straightforward implementation of the W3 grammar is possible, but would 
  %%%   be less than ideal.  In particular, it would be poor at identifying simple 
  %%%   typos and misspellings, or noticing that attrs were specified, but out of 
  %%%   order, etc.
  %%%
  %%%   Accordingly, we introduce Kestrel specific productions, labelled [K1] .. [K21]
  %%%   which are implemented here to factor some original W3 ruls into a parsing 
  %%%   stage using KI rules followed by post-parsing well formedness checks based 
  %%%   perhaps on other W3 rules.  
  %%% 
  %%%   All such substitutions are clearly indicated, and the required well formedness
  %%%   checks are indicated by KC annotations, analogous to WFC and VC annotations.
  %%%
  %%%   Original W3 rules that are replaced by KI rules are flagged with an asterisk.
  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
  %%
  %%  [K2]  DocItems  ::=  DocItem*
  %%
  %%  [K3]  DocItem   ::=  XMLDecl | Comment | PI | S | doctypedecl | element
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort Document = {items : (DocItems | valid_doc_items?)}

  sort DocItems = List DocItem

  sort DocItem = | XMLDecl     XMLDecl
                 | Comment     Comment
                 | PI          PI
                 | WhiteSpace  WhiteSpace
                 | DTD         DocTypeDecl
                 | Element     Element
  
  %%  [KC: Well-Formed Doc]
  def well_formed_doc_items? (items : DocItems) : Boolean =
    let (proper_order?, saw_xml?, saw_dtd?, saw_element?) =
        (foldl (fn (item, (proper_order?, saw_xml?, saw_dtd?, saw_element?)) ->
	       case item of
		 | Comment    _ -> (proper_order?, saw_xml?, saw_dtd?, saw_element?) 
		 | PI         _ -> (proper_order?, saw_xml?, saw_dtd?, saw_element?) 
		 | WhiteSpace _ -> (proper_order?, saw_xml?, saw_dtd?, saw_element?) 
		 | XMLDecl    _ -> (~ (saw_xml? or saw_dtd? or saw_element?),
				    true, saw_dtd?, saw_element?)
		 | DTD        _ -> (~ (saw_dtd? or saw_element?),
				    saw_xml?, true, saw_element?)
		 | Element    _ -> (~ saw_element?, 
				    saw_xml?, saw_dtd?, true)
		 | _            -> (false, saw_xml?, saw_dtd?, saw_element?) % can't happen
		 )
	       (true, false, false, false)
	       items)
    in
    let well_formed? = proper_order? & saw_element? in
    let valid?       = well_formed?  & saw_dtd?     in
    valid?

  %%  [KC: Valid Doc]
  def valid_doc_items? (items : DocItems) : Boolean =
    (well_formed_doc_items? items) 
    &
    (has_dtd? items)

  %% 
  def has_dtd? (items : DocItems) : Boolean =
    foldl (fn (item, saw_dtd?) ->
	   case item of
	     | DTD _ -> true
	     | _     -> saw_dtd?)
          false
	  items

  %% [VC: Root Element Type] 
  def consistent_root_element_type? (items : DocItems) : Boolean =
   case (foldl (fn (item, (root_name, dtd_name)) ->
		case item of
		  | DTD     dtd  -> (root_name,      Some dtd.name)
		  | Element root -> (Some (case root of
					     | Empty tag -> tag.name
					     | Full  element ->
					       element.stag.name),
				     dtd_name)
		  | _ -> (root_name, dtd_name))
	       (None, None)
	       items)
    of 
     | (Some root_name, Some dtd_name) -> root_name = dtd_name
     | _ -> false


  %% Prolog disappears as distinct sort, given [K1] [K2] [K3]
  %% Misc   disappears as distinct sort, given [K1] [K2] [K3]

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          GenericTag                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Rules [K4] -- [K10] simplify the parsing (and especially any associated error reporting) for
  %%  several related constructs given by the W3 grammar as:
  %%
  %%  *[23]  XMLDecl       ::=  '<?xml'     VersionInfo  EncodingDecl? SDDecl?   S? '?>' 
  %%  *[77]  TextDecl      ::=  '<?xml'     VersionInfo? EncodingDecl            S? '?>'         
  %%  *[40]  STag          ::=  '<'  Name   (S Attribute)*                       S?  '>' 
  %%  *[42]  ETag          ::=  '</' Name                                        S?  '>'
  %%  *[44]  EmptyElemTag  ::=  '<'  Name   (S Attribute)*                       S? '/>' 
  %%
  %%  plus several supporting rules for the above
  %%
  %% -------------------------------------------------------------------------------------------------
  %% They are all instances of [K4]:
  %%
  %%  [K4]  GenericTag         ::=  GenericPrefix GenericName GenericAttributes GenericPostfix 
  %%  [K5]  GenericPrefix      ::=  Chars - NmToken
  %%  [K6]  GenericName        ::=  NmToken        
  %%  [K7]  GenericAttributes  ::=  List GenericAttribute
  %%  [K8]  GenericAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%  [K9]  GenericPostfix     ::=  Chars - NmToken
  %% [K10]  QuotedText         ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort GenericTag = {prefix     : GenericPrefix,
		     name       : GenericName,
		     attributes : GenericAttributes,
		     whitespace : WhiteSpace,
		     postfix    : GenericPostfix}

  sort GenericPrefix     = (UChars | generic_prefix?)

  sort GenericName       = NmToken

  sort GenericAttributes = List GenericAttribute

  sort GenericAttribute = {w1    : WhiteSpace,
			   name  : NmToken,
			   w2    : WhiteSpace,
			   %% =
			   w3    : WhiteSpace,
			   value : QuotedText}

  sort GenericPostfix   = (UChars | generic_postfix?)

  op generic_prefix?  : UChars -> Boolean  % complement of names? % TODO
  op generic_postfix? : UChars -> Boolean  % complement of names? % TODO

  sort BoundedText = {qchar : QuoteChar,
		      text  : UString}

  sort QuotedText = (BoundedText | quoted_text?)

  def quoted_text? btext = ~ (member (btext.qchar, btext.text))

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          PI                                                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>' 
  %%  [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%
  %% [K11]  PI        ::= '<?' PITarget (S PIValue)? '?>'           
  %% [K12]  PIValue   ::= Char* - (Char* '?>' Char*)
  %% 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort PI = {target : PITarget,
	     value  : Option (WhiteSpace * PIValue)}

  sort PITarget = (Name    | pi_target?)
  sort PIValue  = (UString | pi_value?)

  def pi_value? ustr = 
    ~ (substring? (ustring "?>", ustr))

  def pi_target? name = 
    ~ (xml_prefix? name)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          External                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %%  Well-formedness constraint: External Subset
  %%
  %%   The external subset, if any, must match the production for extSubset.
  %% 
  %% -------------------------------------------------------------------------------------------------
  %% 
  %%  [30]  extSubset           ::=  TextDecl? extSubsetDecl
  %% 
  %% *[31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)* 
  %%   ==>
  %% [K13]  extSubsetDecl       ::=  ( markupdecl | includeSect | ignoreSect | DeclSep)* 
  %% 
  %%  [61]  conditionalSect     ::=  includeSect | ignoreSect
  %% 
  %%  [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %%  [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>' 
  %% 
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %% 
  %%  [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %% 
  %%  [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% 
  %% *[77]  TextDecl            ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %%   ==>
  %% [K14]  TextDecl            ::=  GenericTag
  %%
  %%                                                             [KC: Proper Text Decl]
  %%  
  %% -------------------------------------------------------------------------------------------------
  %%  
  %%  This is the rule for an external general parsed entity:
  %%  
  %%  [78]  extParsedEnt        ::=  TextDecl? content
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort ExtSubSet = {text  : TextDecl,
		    other : ExtSubsetDecls}
  
  %% -------------------------------------------------------------------------------------------------

  sort TextDecl = (GenericTag | text_decl?) % similar to XMLDecl

  %%  [KC: Proper Text Decl]
  def text_decl? tag = 
    (tag.prefix = ustring "?") & 
    (tag.name   = ustring "xml") & 
    (text_decl_attributes? tag.attributes) &
    (tag.postfix = ustring "?")

  def text_decl_attributes? attrs =
    case attrs of
      | [] -> false
      | xx :: tail -> 
        if version_attribute? xx then
	  (case tail of
	     | yy :: [] -> encoding_attribute? yy 
	     | _ -> false)
	else 
	  (encoding_attribute? xx) & (null tail)

  %% -------------------------------------------------------------------------------------------------

  sort ExtSubsetDecls = List ExtSubsetDecl

  sort ExtSubsetDecl = | Markup  (MarkupDecl | no_pe_reference?)
                       | Include IncludeSect
                       | Ignore  IgnoreSect
                       | DeclSep (DeclSep    | no_pe_reference?)
		    
  op no_pe_reference? : fa (a) a -> Boolean % TODO

  %%  This predicate is a bit tedious, but implements the following constraint documented at
  %%
  %%  [69]  PEReference  ::=  '%' Name ';' 
  %%
  %%                                                             [WFC: In DTD]
  %%  Parameter-entity references may only appear in the DTD.  
  %%  I.e., a PEReference may not appear within a ExtSubsetDecl, so we'll need to recursively search.
  %%  Tedious but straightforward.

  %% -------------------------------------------------------------------------------------------------

  sort IncludeSect = {w1 : WhiteSpace,
		      w2 : WhiteSpace,
		      decl : ExtSubsetDecl}

  %% -------------------------------------------------------------------------------------------------

  sort IgnoreSect = {w1       : WhiteSpace,
		     w2       : WhiteSpace,
		     contents : IgnoreSectContents}


  sort IgnoreSectContents = {prefix   : Ignore,
			     contents : List (IgnoreSectContents * Ignore)}

  sort Ignore = (UString | ignorable?)

  %% TODO
  def ignorable? ustr =
    (~ (sublist? (ustring "<![", ustr)))
    &
    (~ (sublist? (ustring "]]>", ustr)))

  %% -------------------------------------------------------------------------------------------------

  sort extParsedEnt = {text    : TextDecl,
		       content : Content}

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XMLDecl                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% *[23]  XMLDecl       ::=  '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
  %%   ==>
  %% [K15]  XMLDecl       ::=  GenericTag
  %%
  %%                                                             [KC: Proper XML Decl]
  %%
  %% *[24]  VersionInfo   ::=  S 'version' Eq ("'" VersionNum "'" | '"' VersionNum '"')
  %%
  %% *[25]  Eq            ::=  S? '=' S?
  %%
  %% *[26]  VersionNum    ::=  ([a-zA-Z0-9_.:] | '-')+
  %% 
  %% *[32]  SDDecl        ::=  S 'standalone' Eq (("'" ('yes' | 'no') "'") | ('"' ('yes' | 'no') '"'))
  %% 
  %%                                                             [VC: Standalone Document Declaration]
  %% 
  %% *[80]  EncodingDecl  ::=  S 'encoding' Eq ('"' EncName '"' | "'" EncName "'" ) 
  %%
  %% *[81]  EncName       ::=  [A-Za-z] ([A-Za-z0-9._] | '-')* 
  %%                           /* Encoding name contains only Latin characters */
  %% 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort XMLDecl = (GenericTag | xml_decl?)

  %% [KC: Proper XML Decl]
  def xml_decl? tag = 
    (tag.prefix  = ustring "?") & 
    (tag.name    = ustring "xml") & 
    (xml_decl_attributes? tag.attributes) &
    (tag.postfix = ustring "?")

  def xml_decl_attributes? attrs =
    case attrs of
      | [] -> false
      | xx :: tail -> 
        (version_attribute? xx) & 
	(case tail of
	   | [] -> true
	   | yy :: tail -> 
	     (encoding_attribute? yy) &
	     (case tail of
	       | [] -> true
	       | zz :: [] -> 
		(standalone_attribute? zz) 
	       | _ -> false))
  
  %% [24]
  def version_attribute? attribute = 
    (attribute.name = ustring "version") &
    (version_num? attribute.value.text)

  %% [26]
  def version_num? ustr = 
    all? version_num_char? ustr
		  
  %% [32]
  def encoding_attribute?   attribute = 
    (attribute.name = ustring "encoding")
    &
    (legal_encoding_name? attribute.value.text)

  %% [81]
  def legal_encoding_name? (name : UChars) : Boolean =
    case name of
      | char :: tail -> (latin_alphabetic_char? char) & (all? enc_name_char? tail)
      | []           -> false

  %% [32]
  def standalone_attribute? attribute = 
    (attribute.name = ustring "standalone")
    &
    ((attribute.value.text = ustring "yes") or (attribute.value.text = ustring "no"))

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
  %% [28]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>' 
  %%
  %%                                                             [VC:  Root Element Type] 
  %%                                                             [WFC: External Subset]
  %%
  %% [28a]  DeclSep     ::=  PEReference | S    
  %%                                                             [WFC: PE Between Declarations]
  %%
  %% [29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 
  %%
  %%                                                             [VC:  Proper Declaration/PE Nesting] 
  %%                                                             [WFC: PEs in Internal Subset]
  %% 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort DocTypeDecl = {w1          : WhiteSpace,
		      name        : Name,
		      external_id : Option (WhiteSpace * ExternalID),
		      w3          : WhiteSpace,
		      markups     : Option (List (| Decl MarkupDecl | Sep DeclSep) * 
					    WhiteSpace)}

  sort DeclSep = | PEReference PEReference
                 | WhiteSpace  WhiteSpace

  sort MarkupDecl = | Element      ElementDecl
                    | Attributes   AttlistDecl
                    | Entity       EntityDecl
                    | Notation     NotationDecl
                    | PI           PI
                    | Comment      Comment

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD ElementDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>' 
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %% [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children 
  %%
  %% [47]  children     ::=  (choice | seq) ('?' | '*' | '+')? 
  %%
  %% [48]  cp           ::=  (Name | choice | seq) ('?' | '*' | '+')? 
  %%
  %% [49]  choice       ::=  '(' S? cp ( S? '|' S? cp )+ S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%
  %% [50]  seq          ::=  '(' S? cp ( S? ',' S? cp )* S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %% [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')' 
  %%
  %%                                                             [VC: Proper Group/PE Nesting] 
  %%                                                             [VC: No Duplicate Types]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort ElementDecl = {w1       : WhiteSpace,
		      name     : Name,
		      w2       : WhiteSpace,
		      contents : ContentSpec,
		      w3       : WhiteSpace}

  sort ContentSpec = | Empty
                     | Any
                     | Mixed    Mixed
                     | Children Children

  sort Mixed = | Names   Mixed_With_Names
               | NoNames Mixed_Without_Names

  sort Mixed_With_Names = {w1    : WhiteSpace,
			   names : List (WhiteSpace * WhiteSpace * Name),
			   w2    : WhiteSpace}
		
  sort Mixed_Without_Names = {w1 : WhiteSpace,
			      w2 : WhiteSpace}
		
  sort Children = {body : | Choice Choice | Seq Seq,
		   rule : | Question | Star | Plus}
   
  sort Choice = {w1     : WhiteSpace,
		 first  : CP,
		 others : NE_List (WhiteSpace * WhiteSpace * CP),
                 w2     : WhiteSpace}                 

  sort CP = {body : | Name Name | Choice Choice | Seq Seq,
	     rule : | Question | Star | Plus}
   
  sort Seq = {w1     : WhiteSpace,
	      first  : CP,
	      others : List (WhiteSpace * WhiteSpace * CP),
	      w2     : WhiteSpace}


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD AttListDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
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
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort AttlistDecl = {w1   : WhiteSpace,
		      name : Name,
		      defs : List AttDef,
		      w2   : WhiteSpace}

  sort AttDef = {w1      : WhiteSpace,
		 name    : Name,
		 w2      : WhiteSpace,
		 type    : AttType,
		 w3      : WhiteSpace,
		 default : DefaultDecl}


  sort AttType = | String     
                 %%  Tokenized 
                 | ID 
                 | IDRef
                 | IDRefs 
                 | Entity 
                 | Entities 
                 | NmToken 
                 | NmTokens
                 %%  EnumeratedType
                 | Notation    NotationType
                 | Enumeration Enumeration
  
  sort NotationType = {w1     : WhiteSpace,
		       w2     : WhiteSpace,
		       first  : Name,
		       others : List (WhiteSpace * WhiteSpace * Name),
		       w3     : WhiteSpace}

  sort Enumeration = {w1     : WhiteSpace,
		      first  : NmToken,
		      others : List (WhiteSpace * WhiteSpace * NmToken),
		      w2     : WhiteSpace}

  sort DefaultDecl = | Required
                     | Implied 
                     | Fixed    (Option WhiteSpace) * AttValue


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD EntityDecl                                                                      %%%
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

  sort EntityDecl = | GE GEDecl
                    | PE PEDecl

  sort GEDecl = {w1   : WhiteSpace,
		 name : Name,
		 w2   : WhiteSpace,
		 edef : EntityDef,
		 w3   : WhiteSpace}

  sort EntityDef = | Value    EntityValue
                   | External (ExternalID * Option NDataDecl)

  sort NDataDecl = {w1   : WhiteSpace,
		    w2   : WhiteSpace,
		    name : Name}

  sort PEDecl = {w1    : WhiteSpace,
		 w2    : WhiteSpace,
		 name  : Name,
		 w3    : WhiteSpace,
		 pedef : PEDef,
		 w4    : WhiteSpace}

  sort PEDef = | Value    EntityValue
               | External ExternalID 


  %% ----------------------------------------------------------------------------------------------------

  sort GenericID = {w1     : WhiteSpace,
		    public : Option PubidLiteral,
		    w2     : WhiteSpace,
		    system : Option SystemLiteral}
		   
  sort ExternalID = (GenericID | external_id?)
  sort PublicID   = (GenericID | public_id?)

  %% [KC: At Least System]
  def external_id? generic =
    case generic.system of
      | Some _ -> true
      | _ -> false

  %% [KC: Just PUBLIC]
  def public_id? generic =
    case (generic.system, generic.public) of
	| (None, Some _) -> true
	| _ -> false

  %% ----------------------------------------------------------------------------------------------------

  sort NotationDecl = {w1   : WhiteSpace,
		       name : Name,
		       w2   : WhiteSpace,
		       id   : GenericID,
		       w3   : WhiteSpace}


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Element                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% [39]  element  ::=  EmptyElemTag | STag content ETag 
  %%                                                             [WFC: Element Type Match] 
  %%                                                             [VC:  Element Valid]
  %%
  %% *[40]  STag          ::=  '<' Name (S Attribute)* S? '>' 
  %%                                                             [WFC: Unique Att Spec]
  %%   ==>
  %% [K19]  STag          ::=  GenericTag                            
  %%                                                             [KC:  Proper Start Tag]
  %%                                                             [WFC: Unique Att Spec]
  %% 
  %%  [41]  Attribute     ::=  Name Eq AttValue 
  %%                                                             [VC:  Attribute Value Type]
  %%                                                             [WFC: No External Entity References]
  %%                                                             [WFC: No < in Attribute Values]
  %%
  %% *[42]  ETag          ::=  '</' Name S? '>'
  %%   ==>
  %% [K20]  ETag          ::=  GenericTag                   
  %%                                                             [KC:  Proper End Tag]
  %%
  %%  Since the chardata in [43] is typically used for indentation, 
  %%  it makes more sense to group it as in [K18]:
  %%
  %% *[43]  content       ::=  CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
  %%   ==>
  %% [K21]  content       ::=  (CharData? (element | Reference | CDSect | PI | Comment))* CharData?
  %% 
  %% *[44]  EmptyElemTag  ::=  '<' Name (S Attribute)* S? '/>' 60]
  %%                                                             [WFC: Unique Att Spec]
  %%   ==>
  %% [K22]  EmptyElemTag  ::=  GenericTag
  %%                                                             [KC:  Proper Empty Tag]
  %%                                                             [WFC: Unique Att Spec]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort Element = | Empty EmptyElemTag
                 | Full  (PossibleElement | element_types_match?)

  sort PossibleElement = {stag    : STag,
			  content : Content,
			  etag    : ETag}

  %% [WFC: Element Type Match]
  def element_types_match? elt =
    elt.stag.name = elt.etag.name

  %% ----------------------------------------------------------------------------------------------------

  sort STag = ((GenericTag | start_tag?) | unique_attributes?)

  %%  [KC: Proper start tag]
  def start_tag? tag = 
    (null tag.prefix)          & 
    (~ (xml_prefix? tag.name)) &
    (null tag.postfix)  

  def xml_prefix? name = 
    case name of
      %% Note: Formal Spec only excludes 3 char strings, but English spec 
      %%       indicates that any string starting with xml is forbidden.
      | c0 :: c1 :: c2 :: _ ->  
        (((c0 = 88 (* X *)) or (c0 = 120 (* x *)))
	 &
	 ((c1 = 77 (* M *)) or (c0 = 109 (* m *)))
	 &
	 ((c2 = 76 (* L *)) or (c0 = 108 (* l *))))
      | _ -> false
      
  %% [WFC: Unique Att Spec]
  def unique_attributes? tag =
    let (all_unique?, _) = (foldl (fn (attr, (all_unique?, names)) -> 
				   if all_unique? then
				     if member (attr.name, names) then
				       (false, [])
				     else
				       (true, cons (attr.name, names))
				   else
				     (false, []))
			          (true, [])
				  tag.attributes)
    in
      all_unique?

  %% ----------------------------------------------------------------------------------------------------

  sort Attribute = {name     : Name,
		    w1       : WhiteSpace,
		    %% =
		    w2       : WhiteSpace,
		    value    : AttValue}

  %% ----------------------------------------------------------------------------------------------------

  sort ETag = (GenericTag | end_tag?)

  %%  [KC: proper end tag]
  def end_tag? tag = 
    (tag.prefix = [47])        & 
    (~ (xml_prefix? tag.name)) &
    (null tag.attributes)      & 
    (null tag.postfix)

  %% ----------------------------------------------------------------------------------------------------

  sort Content = {items   : List (Option CharData * Content_Item),
		  trailer : Option CharData}

  sort Content_Item = | Element   Element 
                      | Reference Reference 
                      | CDSect    CDSect 
                      | PI        PI
                      | Comment   Comment

  %% ----------------------------------------------------------------------------------------------------

  sort EmptyElemTag = ((GenericTag | empty_tag?) | unique_attributes?)  

  %% [KC: proper empty tag]
  def empty_tag? tag = 
    (null tag.prefix)          & 
    (~ (xml_prefix? tag.name)) &
    (tag.postfix = [47])          (* '/' *) 

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Character_Strings                                                                   %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %%
  %% [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %%
  %% [18]  CDSect    ::=  CDStart CData CDEnd 
  %% [19]  CDStart   ::=  '<![CDATA[' 
  %% [20]  CData     ::=  (Char* - (Char* ']]>' Char*)) 
  %% [21]  CDEnd     ::=  ']]>'
  %%
  %%  Note that the anonymous rule about characters (see section below on WFC's) implicitly 
  %%  restricts the characters that may appear in CharData to be Char's.
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort CharData = (UString | char_data?)

  %% [14]
  def char_data? ustr = 
    (all? char_data_char? ustr)                 % i.e.g, char?, but not '<' or '%'
    &				    
    ~ (substring? (ustring "]]>", ustr))

  %% ----------------------------------------------------------------------------------------------------

  sort Comment = (UString | comment?)

  %% [15]
  def comment? ustr = 
    ~ (substring? (ustring "--", ustr))

  %% ----------------------------------------------------------------------------------------------------


  sort CDSect = {cdata : (UString | cdata?)}

  %% [19] [20] [21]
  def cdata? ustr =
    ~ (substring? (ustring "]]>", ustr))

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Literals                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %%  [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %%  [11]  SystemLiteral   ::=  ('"' [^"]* '"') | ("'" [^']* "'") 
  %%   ==>
  %% [K23]  SystemuLiteral  ::=  QuotedText
  %%                
  %%  [12]  PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'" 
  %%   ==>
  %% [K24]  PubidLiteral    ::=  QuotedText
  %%                
  %%                                                             [KC: Proper Pubid Literal]   
  %%
  %%  [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort EntityValue = {qchar : QuoteChar,
		      items : List EntityValue_Item}

  sort EntityValue_Item = | NonRef UString
                          | PERef  PEReference
                          | Ref    Reference

  sort AttValue = {qchar : QuoteChar,
		   items : List AttValue_Item}

  sort AttValue_Item = | NonRef UString
                       | Ref    Reference


  sort SystemLiteral = (QuotedText | legal_SystemLiteral?)
  sort PubidLiteral  = (QuotedText | legal_PubidLiteral?)

  def legal_SystemLiteral? quoted_text =
    true

  def legal_PubidLiteral? quoted_text =
    (all? pubid_char? quoted_text.text) 	  			

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          References                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';' 
  %%
  %%                                                             [WFC: Legal Character]
  %%
  %% [67]  Reference    ::=  EntityRef | CharRef
  %%
  %% [68]  EntityRef    ::=  '&' Name ';' 
  %%
  %%                                                             [WFC: Entity Declared]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: Parsed Entity] 
  %%                                                             [WFC: No Recursion]
  %%
  %% [69]  PEReference  ::=  '%' Name ';' 
  %%
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: No Recursion]
  %%                                                             [WFC: In DTD]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort PEReference = {name : (Name | entity_declared?)}

  sort Reference = | Entity EntityRef
                   | Char   CharRef

  sort EntityRef = {name : (Name | entity_declared?)}

  
  sort CharRef = {style : | Decimal | Hex,
		  %% note that char? can be true for large values (> 2^16) up to #x10FFFF
		  char  : (UChar | char?)}

  %% [VC:  Entity Declared]:
  op entity_declared? : Name -> Boolean   % tricky  % TODO

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Names                                                                               %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [4]  NameChar  ::=  Letter | Digit | '.' | '-' | '_' | ':' | CombiningChar | Extender
  %%  [5]  Name      ::=  (Letter | '_' | ':') (NameChar)*
  %%  [6]  Names     ::=  Name (S Name)*
  %%  [7]  Nmtoken   ::=  (NameChar)+
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort Names = Name * List (WhiteSpace * Name)
  sort Name  = (UString | name?)

  %% [5]
  def name? ustr = 
    case ustr of
      | char :: tail ->  ((letter? char) or (char = 95 (* _ *)) or (char = 58 (* : *)))
	&
	(all? name_char? tail)
      | _ ->
	false

  sort NmTokens = NmToken * List (WhiteSpace * NmToken)
  sort NmToken  = (UString | nm_token?)

  %% [7]
  def nm_token? ustr =
    all? name_char? ustr

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Chars                                                                               %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %%  [2]  Char          ::=  #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF] 
  %%                          /* any Unicode character, excluding the surrogate blocks, FFFE, and FFFF. */
  %%
  %%  [3]  S             ::=  (#x20 | #x9 | #xD | #xA)+
  %%
  %% [84]  Letter        ::=  BaseChar | Ideographic
  %%
  %% [85]  BaseChar      ::=  [#x0041-#x005A] | [#x0061-#x007A] |   /* ascii: [A-Z] [a-z] */
  %%                            /* annotated vowels (umlaut, circumflex, ...) */
  %%                          [#x00C0-#x00D6] | [#x00D8-#x00F6] | [#x00F8-#x00FF] |  
  %%                            /* lots of odd characters */
  %%                          [#x0100-#x0131] | [#x0134-#x013E] | [#x0141-#x0148] | 
  %%                          [#x014A-#x017E] | [#x0180-#x01C3] | [#x01CD-#x01F0] | [#x01F4-#x01F5] | 
  %%                          [#x01FA-#x0217] | [#x0250-#x02A8] | [#x02BB-#x02C1] | #x0386 | 
  %%                          [#x0388-#x038A] | #x038C | [#x038E-#x03A1] | [#x03A3-#x03CE] | 
  %%                          [#x03D0-#x03D6] | #x03DA | #x03DC | #x03DE | #x03E0 | [#x03E2-#x03F3] | 
  %%                          [#x0401-#x040C] | [#x040E-#x044F] | [#x0451-#x045C] | [#x045E-#x0481] | 
  %%                          [#x0490-#x04C4] | [#x04C7-#x04C8] | [#x04CB-#x04CC] | [#x04D0-#x04EB] | 
  %%                          [#x04EE-#x04F5] | [#x04F8-#x04F9] | [#x0531-#x0556] | #x0559 | 
  %%                          [#x0561-#x0586] | [#x05D0-#x05EA] | [#x05F0-#x05F2] | [#x0621-#x063A] | 
  %%                          [#x0641-#x064A] | [#x0671-#x06B7] | [#x06BA-#x06BE] | [#x06C0-#x06CE] | 
  %%                          [#x06D0-#x06D3] | #x06D5 | [#x06E5-#x06E6] | [#x0905-#x0939] | #x093D | 
  %%                          [#x0958-#x0961] | [#x0985-#x098C] | [#x098F-#x0990] | [#x0993-#x09A8] | 
  %%                          [#x09AA-#x09B0] | #x09B2 | [#x09B6-#x09B9] | [#x09DC-#x09DD] | 
  %%                          [#x09DF-#x09E1] | [#x09F0-#x09F1] | [#x0A05-#x0A0A] | [#x0A0F-#x0A10] | 
  %%                          [#x0A13-#x0A28] | [#x0A2A-#x0A30] | [#x0A32-#x0A33] | [#x0A35-#x0A36] | 
  %%                          [#x0A38-#x0A39] | [#x0A59-#x0A5C] | #x0A5E | [#x0A72-#x0A74] | 
  %%                          [#x0A85-#x0A8B] | #x0A8D | [#x0A8F-#x0A91] | [#x0A93-#x0AA8] | 
  %%                          [#x0AAA-#x0AB0] | [#x0AB2-#x0AB3] | [#x0AB5-#x0AB9] | #x0ABD | #x0AE0 | 
  %%                          [#x0B05-#x0B0C] | [#x0B0F-#x0B10] | [#x0B13-#x0B28] | [#x0B2A-#x0B30] | 
  %%                          [#x0B32-#x0B33] | [#x0B36-#x0B39] | #x0B3D | [#x0B5C-#x0B5D] | 
  %%                          [#x0B5F-#x0B61] | [#x0B85-#x0B8A] | [#x0B8E-#x0B90] | [#x0B92-#x0B95] | 
  %%                          [#x0B99-#x0B9A] | #x0B9C | [#x0B9E-#x0B9F] | [#x0BA3-#x0BA4] | 
  %%                          [#x0BA8-#x0BAA] | [#x0BAE-#x0BB5] | [#x0BB7-#x0BB9] | [#x0C05-#x0C0C] | 
  %%                          [#x0C0E-#x0C10] | [#x0C12-#x0C28] | [#x0C2A-#x0C33] | [#x0C35-#x0C39] | 
  %%                          [#x0C60-#x0C61] | [#x0C85-#x0C8C] | [#x0C8E-#x0C90] | [#x0C92-#x0CA8] | 
  %%                          [#x0CAA-#x0CB3] | [#x0CB5-#x0CB9] | #x0CDE | [#x0CE0-#x0CE1] | 
  %%                          [#x0D05-#x0D0C] | [#x0D0E-#x0D10] | [#x0D12-#x0D28] | [#x0D2A-#x0D39] | 
  %%                          [#x0D60-#x0D61] | [#x0E01-#x0E2E] | #x0E30 | [#x0E32-#x0E33] | 
  %%                          [#x0E40-#x0E45] | [#x0E81-#x0E82] | #x0E84 | [#x0E87-#x0E88] | #x0E8A | 
  %%                          #x0E8D | [#x0E94-#x0E97] | [#x0E99-#x0E9F] | [#x0EA1-#x0EA3] | #x0EA5 | 
  %%                          #x0EA7 | [#x0EAA-#x0EAB] | [#x0EAD-#x0EAE] | #x0EB0 | [#x0EB2-#x0EB3] | 
  %%                          #x0EBD | [#x0EC0-#x0EC4] | [#x0F40-#x0F47] | [#x0F49-#x0F69] | 
  %%                          [#x10A0-#x10C5] | [#x10D0-#x10F6] | #x1100 | [#x1102-#x1103] | 
  %%                          [#x1105-#x1107] | #x1109 | [#x110B-#x110C] | [#x110E-#x1112] | #x113C | 
  %%                          #x113E | #x1140 | #x114C | #x114E | #x1150 | [#x1154-#x1155] | #x1159 | 
  %%                          [#x115F-#x1161] | #x1163 | #x1165 | #x1167 | #x1169 | [#x116D-#x116E] | 
  %%                          [#x1172-#x1173] | #x1175 | #x119E | #x11A8 | #x11AB | [#x11AE-#x11AF] | 
  %%                          [#x11B7-#x11B8] | #x11BA | [#x11BC-#x11C2] | #x11EB | #x11F0 | #x11F9 | 
  %%                          [#x1E00-#x1E9B] | [#x1EA0-#x1EF9] | [#x1F00-#x1F15] | [#x1F18-#x1F1D] | 
  %%                          [#x1F20-#x1F45] | [#x1F48-#x1F4D] | [#x1F50-#x1F57] | #x1F59 | #x1F5B | 
  %%                          #x1F5D | [#x1F5F-#x1F7D] | [#x1F80-#x1FB4] | [#x1FB6-#x1FBC] | #x1FBE | 
  %%                          [#x1FC2-#x1FC4] | [#x1FC6-#x1FCC] | [#x1FD0-#x1FD3] | [#x1FD6-#x1FDB] | 
  %%                          [#x1FE0-#x1FEC] | [#x1FF2-#x1FF4] | [#x1FF6-#x1FFC] | #x2126 | 
  %%                          [#x212A-#x212B] | #x212E | [#x2180-#x2182] | [#x3041-#x3094] | 
  %%                          [#x30A1-#x30FA] | [#x3105-#x312C] | 
  %%                          [#xAC00-#xD7A3]
  %%
  %% [86]  Ideographic   ::=  [#x4E00-#x9FA5] | #x3007 | [#x3021-#x3029]
  %% 
  %% [87]  CombiningChar ::=  [#x0300-#x0345] | [#x0360-#x0361] | [#x0483-#x0486] | [#x0591-#x05A1] | 
  %%                          [#x05A3-#x05B9] | [#x05BB-#x05BD] | #x05BF | [#x05C1-#x05C2] | #x05C4 | 
  %%                          [#x064B-#x0652] | #x0670 | [#x06D6-#x06DC] | [#x06DD-#x06DF] | 
  %%                          [#x06E0-#x06E4] | [#x06E7-#x06E8] | [#x06EA-#x06ED] | [#x0901-#x0903] | 
  %%                          #x093C | [#x093E-#x094C] | #x094D | [#x0951-#x0954] | [#x0962-#x0963] | 
  %%                          [#x0981-#x0983] | #x09BC | #x09BE | #x09BF | [#x09C0-#x09C4] | 
  %%                          [#x09C7-#x09C8] | [#x09CB-#x09CD] | #x09D7 | [#x09E2-#x09E3] | #x0A02 | 
  %%                          #x0A3C | #x0A3E | #x0A3F | [#x0A40-#x0A42] | [#x0A47-#x0A48] | 
  %%                          [#x0A4B-#x0A4D] | [#x0A70-#x0A71] | [#x0A81-#x0A83] | #x0ABC | 
  %%                          [#x0ABE-#x0AC5] | [#x0AC7-#x0AC9] | [#x0ACB-#x0ACD] | [#x0B01-#x0B03] | 
  %%                          #x0B3C | [#x0B3E-#x0B43] | [#x0B47-#x0B48] | [#x0B4B-#x0B4D] | 
  %%                          [#x0B56-#x0B57] | [#x0B82-#x0B83] | [#x0BBE-#x0BC2] | [#x0BC6-#x0BC8] | 
  %%                          [#x0BCA-#x0BCD] | #x0BD7 | [#x0C01-#x0C03] | [#x0C3E-#x0C44] | 
  %%                          [#x0C46-#x0C48] | [#x0C4A-#x0C4D] | [#x0C55-#x0C56] | [#x0C82-#x0C83] | 
  %%                          [#x0CBE-#x0CC4] | [#x0CC6-#x0CC8] | [#x0CCA-#x0CCD] | [#x0CD5-#x0CD6] | 
  %%                          [#x0D02-#x0D03] | [#x0D3E-#x0D43] | [#x0D46-#x0D48] | [#x0D4A-#x0D4D] | 
  %%                          #x0D57 | #x0E31 | [#x0E34-#x0E3A] | [#x0E47-#x0E4E] | #x0EB1 | 
  %%                          [#x0EB4-#x0EB9] | [#x0EBB-#x0EBC] | [#x0EC8-#x0ECD] | [#x0F18-#x0F19] | 
  %%                          #x0F35 | #x0F37 | #x0F39 | #x0F3E | #x0F3F | [#x0F71-#x0F84] | 
  %%                          [#x0F86-#x0F8B] | [#x0F90-#x0F95] | #x0F97 | [#x0F99-#x0FAD] | 
  %%                          [#x0FB1-#x0FB7] | #x0FB9 | [#x20D0-#x20DC] | #x20E1 | [#x302A-#x302F] | 
  %%                          #x3099 | #x309A
  %%
  %% [88]  Digit         ::=  [#x0030-#x0039] |  /* ascii [0-9] */
  %%                          [#x0660-#x0669] | [#x06F0-#x06F9] | [#x0966-#x096F] | 
  %%                          [#x09E6-#x09EF] | [#x0A66-#x0A6F] | [#x0AE6-#x0AEF] | [#x0B66-#x0B6F] | 
  %%                          [#x0BE7-#x0BEF] | [#x0C66-#x0C6F] | [#x0CE6-#x0CEF] | [#x0D66-#x0D6F] | 
  %%                          [#x0E50-#x0E59] | [#x0ED0-#x0ED9] | [#x0F20-#x0F29]
  %%
  %% [89]  Extender      ::=  #x00B7 | #x02D0 | #x02D1 | #x0387 | #x0640 | #x0E46 | #x0EC6 | #x3005 |
  %%                          [#x3031-#x3035] | [#x309D-#x309E] | [#x30FC-#x30FE]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% These are all handwritten as vector-of-boolean accesses

  op char?                  : UChar -> Boolean    % [2]   % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op white_char?            : UChar -> Boolean    % [3]   % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op letter?                : UChar -> Boolean    % [84]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op base_char?             : UChar -> Boolean    % [85]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op ideographic_char?      : UChar -> Boolean    % [86]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op combining_char?        : UChar -> Boolean    % [87]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op digit?                 : UChar -> Boolean    % [88]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op extender_char?         : UChar -> Boolean    % [89]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op name_char?             : UChar -> Boolean    % [4]   % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op name_start_char?       : UChar -> Boolean    % [5]   % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op pubid_char?            : UChar -> Boolean    % [13]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op hex_digit?             : UChar -> Boolean    % [66]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op version_num_char?      : UChar -> Boolean    % [26]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op enc_name_char?         : UChar -> Boolean    % [81]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op latin_alphabetic_char? : UChar -> Boolean    % [81]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp
  op char_data_char?        : UChar -> Boolean    % [14]  % See /Languages/XML/Handwritten/Lisp/Chars.lisp

  %% [9] [10] [11] [12] [24] [32] [80] [K10]  
  def quote_char? (char : UChar) : Boolean =
    (char = UChar.double_quote) or
    (char = UChar.apostrophe)

  sort WhiteChar            = (UChar | white_char?)            % [3]
  sort Letter               = (UChar | letter?)                % [84]
  sort BaseChar             = (UChar | base_char?)             % [85]
  sort IdeographicChar      = (UChar | ideographic_char?)      % [86]
  sort CombingingChar       = (UChar | combining_char?)        % [87]
  sort Digit                = (UChar | digit?)                 % [88]
  sort ExtenderChar         = (UChar | extender_char?)         % [89]
  sort NameChar             = (UChar | name_char?)             % [4]
  sort NameStartChar        = (UChar | name_start_char?)       % [5]
  sort PubidChar            = (UChar | pubid_char?)            % [13]
  sort HexDigit             = (UChar | hex_digit?)             % [66]
  sort VersionNumChar       = (UChar | version_num_char?)      % [26]
  sort EncNameChar          = (UChar | enc_name_char?)         % [81]
  sort LatinAlphabeticChar? = (UChar | latin_alphabetic_char?) % [81]
  sort QuoteChar            = (UChar | quote_char?)            % [9] [10] [11] [12] [24] [32] [80] [K10]  

  sort WhiteSpace = (UChars | whitespace?)    % [3]
  def whitespace? (chars : UChars) : Boolean =
    all? white_char? chars

  def null_whitespace : WhiteSpace = []

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Table of WFC, KC, and VC entries                                                    %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Well-Formedness Conditions:
  %%
  %%  anonymous rule given at http://www.w3.org/TR/REC-xml#dt-character
  %%
  %%  [Definition: A parsed entity contains text, a sequence of characters, which may represent 
  %%  markup or character data.] [Definition: A character is an atomic unit of text as specified 
  %%  by ISO/IEC 10646 [ISO/IEC 10646] (see also [ISO/IEC 10646-2000]). Legal characters are tab,
  %%  carriage return, line feed, and the legal characters of Unicode and ISO/IEC 10646. 
  %%  The versions of these standards cited in A.1 Normative References were current at the time 
  %%  this document was prepared. New characters may be added to these standards by amendments 
  %%  or new editions. Consequently, XML processors must accept any character in the range specified 
  %%  for Char. The use of "compatibility characters", as defined in section 6.8 of [Unicode] 
  %%  (see also D21 in section 3.6 of [Unicode3]), is discouraged.]
  %%
  %%  [WFC: External Subset]                        [28]
  %%
  %%    The external subset, if any, must match the production for extSubset.
  %%
  %%  [WFC: PE Between Declarations]                [28a]
  %%
  %%    The replacement text of a parameter entity reference in a DeclSep must match the production
  %%    extSubsetDecl.
  %%
  %%  [WFC: PEs in Internal Subset]                 [29]
  %%
  %%    In the internal DTD subset, parameter-entity references can occur only where markup
  %%    declarations can occur, not within markup declarations. (This does not apply to references
  %%    that occur in external parameter entities or to the external subset.)
  %%
  %%  [WFC: No < in Attribute Values]               [60]  [41]
  %%
  %%    The replacement text of any entity referred to directly or indirectly in an attribute value
  %%     must not contain a <.
  %%
  %%  [WFC: Element Type Match]                     [39]  -- element_types_match?
  %% 
  %%    The Name in an element's end-tag must match the element type in the start-tag.
  %% 
  %%  [WFC: Unique Att Spec]                       *[40] *[44] [K16] [K19] -- unique_attributes?
  %%
  %%    No attribute name may appear more than once in the same start-tag or empty-element tag.
  %%
  %%  [WFC: No External Entity References]          [41]
  %%
  %%    Attribute values cannot contain direct or indirect entity references to external entities.
  %%
  %%  [WFC: Legal Character]                        [66] -- char?
  %%
  %%    Characters referred to using character references must match the production for Char.
  %%
  %%  [WFC: Entity Declared]                        [68]
  %%
  %%    In a document without any DTD, a document with only an internal DTD subset which contains no 
  %%    parameter entity references, or a document with "standalone='yes'", for an entity reference 
  %%    that does not occur within the external subset or a parameter entity, the Name given in the 
  %%    entity reference must match that in an entity declaration that does not occur within the 
  %%    external subset or a parameter entity, except that well-formed documents need not declare any
  %%    of the following entities: amp, lt, gt, apos, quot. The declaration of a general entity must
  %%    precede any reference to it which appears in a default value in an attribute-list declaration.
  %%
  %%  [WFC: Parsed Entity]                          [68]   
  %%
  %%    An entity reference must not contain the name of an unparsed entity. Unparsed entities may 
  %%    be referred to only in attribute values declared to be of type ENTITY or ENTITIES.
  %%
  %%  [WFC: No Recursion]                           [68]  [69]
  %%
  %%    A parsed entity must not contain a recursive reference to itself, either directly or 
  %%    indirectly.
  %%
  %%  [WFC: In DTD]                                 [69] (really [31] [K11]) -- no_pe_reference?
  %%
  %%    Parameter-entity references may only appear in the DTD.  
  %%    
  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [KC: Well-Formed Doc]                         [K1]  -- well_formed_doc?
  %%
  %%    at most one XMLDecl
  %%    at most one doctypedecl
  %%    exactly one element
  %%    XMLDecl appears first (if at all)
  %%    doctypedecl precees element
  %%
  %%  [KC: Valid Doc]                               [K1]  -- valid_doc?
  %%    
  %%    exactly one doctypedecl
  %%
  %%  [KC: Proper Text Decl]                       [K14]  -- text_decl?
  %%
  %%    prefix      = '?'
  %%    name        = 'xml'
  %%    attributes  = version? encoding
  %%    postfix     = '?'
  %%
  %%  [KC: Proper XML Decl]                        [K15] -- xml_decls?
  %%
  %%    prefix     = '?'
  %%    name       = 'xml']
  %%    attributes = version encoding? standalone?
  %%    postfix    = '?'
  %%
  %%  [KC: At Least SYSTEM]                        [K16] -- external_id?
  %%
  %%    some system literal
  %%    (optional public literal)
  %%
  %%  [KC: Just PUBLIC]                            [K17] -- public_id?
  %%
  %%    no sytem literal
  %%    public literal
  %%
  %%  [KC: Proper Start Tag]                       [K19] -- start_tag?
  %%
  %%    prefix     = ''
  %%    name       not = 'xml'
  %%    postfix    = ''
  %%
  %%  [KC: Proper End   Tag]                       [K20] -- end_tag?
  %%
  %%    prefix     = '/'
  %%    name       not = 'xml'
  %%    postfix    = ''
  %%
  %%  [KC: Proper Empty Tag]                       [K22] -- empty_tag?
  %%
  %%    prefix     = ''
  %%    name       not = 'xml'
  %%    postfix    = '/'
  %%
  %%  [KC: Proper Pubid Literal]                   [K24] -- legal_PubidLiteral?
  %%
  %%    all chars are PubidChar's
  %%
  %%  ------------------------------------------------------------------------------------------------
  %%
  %%  Validity Conditions:
  %%   
  %%  [VC: Proper Conditional Section/PE Nesting]   [62]  [63]
  %%
  %%    If any of the "<![", "[", or "]]>" of a conditional section is contained in the replacement 
  %%    text for a parameter-entity reference, all of them must be contained in the same replacement
  %%     text.
  %%
  %%  [VC: Standalone Document Declaration]        *[32]
  %%
  %%    The standalone document declaration must have the value "no" if any external markup 
  %%    declarations contain declarations of:
  %%
  %%     *  attributes with default values, if elements to which these attributes apply appear 
  %%        in the document without specifications of values for these attributes, or
  %%
  %%     *  entities (other than amp, lt, gt, apos, quot), if references to those entities appear 
  %%        in the document, or
  %%
  %%     *  attributes with values subject to normalization, where the attribute appears in the 
  %%        document with a value which will change as a result of normalization, or
  %%
  %%     *  element types with element content, if white space occurs directly within any instance 
  %%        of those types.
  %%
  %%  [VC: Root Element Type]                       [28] (really K1) -- consistent_root_element_type?
  %% 
  %%    The Name in the document type declaration must match the element type of the root element.
  %%
  %%  [VC: Proper Declaration/PE Nesting]           [29]
  %%
  %%    Parameter-entity replacement text must be properly nested with markup declarations. 
  %%
  %%    That is to say, if either the first character or the last character of a markup declaration 
  %%    (markupdecl above) is contained in the replacement text for a parameter-entity reference, 
  %%    both must be contained in the same replacement text.
  %%
  %%  [VC: Unique Element Type Declaration]         [45]
  %%
  %%    No element type may be declared more than once.
  %%
  %%  [VC: Proper Group/PE Nesting]                 [49] [50] [51]
  %%
  %%    Parameter-entity replacement text must be properly nested with parenthesized groups. 
  %%
  %%    That is to say, if either of the opening or closing parentheses in a choice, seq, or Mixed
  %%    construct is contained in the replacement text for a parameter entity, both must be contained
  %%    in the same replacement text.
  %%
  %%    For interoperability, if a parameter-entity reference appears in a choice, seq, or Mixed
  %%    construct, its replacement text should contain at least one non-blank character, and neither
  %%    the first nor last non-blank character of the replacement text should be a connector (| or ,).
  %%
  %%  [VC: No Duplicate Types]                      [51]
  %%
  %%    The same name must not appear more than once in a single mixed-content declaration.
  %%
  %%  [VC: ID]                                      [56]
  %%
  %%    Values of type ID must match the Name production. A name must not appear more than once in an
  %%    XML document as a value of this type; i.e., ID values must uniquely identify the elements
  %%    which bear them.
  %%
  %%  [VC: One ID per Element Type]                 [56]
  %%
  %%    No element type may have more than one ID attribute specified.
  %%
  %%  [VC: ID Attribute Default]                    [56]
  %%
  %%    An ID attribute must have a declared default of #IMPLIED or #REQUIRED.
  %%
  %%  [VC: IDREF]                                   [56]
  %%
  %%    Values of type IDREF must match the Name production, and values of type IDREFS must match 
  %%    Names; each Name must match the value of an ID attribute on some element in the XML document;
  %%     i.e. IDREF values must match the value of some ID attribute.
  %%
  %%  [VC: Entity Name]                             [56]
  %%
  %%    Values of type ENTITY must match the Name production, values of type ENTITIES must match 
  %%    Names; each Name must match the name of an unparsed entity declared in the DTD.
  %%
  %%  [VC: Name Token]                              [56]
  %%  
  %%    Values of type NMTOKEN must match the Nmtoken production; values of type NMTOKENS must match 
  %%    Nmtokens.
  %%
  %%  [VC: Notation Attributes]                     [58]
  %%
  %%    Values of this type must match one of the notation names included in the declaration;
  %%    all notation names in the declaration must be declared.
  %%
  %%  [VC: One Notation Per Element Type]           [58]
  %%
  %%    No element type may have more than one NOTATION attribute specified.
  %%
  %%  [VC: No Notation on Empty Element]            [58]
  %%  
  %%    For compatibility, an attribute of type NOTATION must not be declared on an element declared 
  %%    EMPTY.
  %%  
  %%  [VC: Enumeration]                             [59]
  %%  
  %%    Values of this type must match one of the Nmtoken tokens in the declaration.
  %%
  %%  [VC: Required Attribute]                      [60]
  %%
  %%    If the default declaration is the keyword #REQUIRED, then the attribute must be specified for
  %%    all elements of the type in the attribute-list declaration.
  %%
  %%  [VC: Attribute Default Legal]                 [60]
  %%
  %%    The declared default value must meet the lexical constraints of the declared attribute type.
  %%
  %%  [VC: Fixed Attribute Default]                 [60]
  %%  
  %%    If an attribute has a default value declared with the #FIXED keyword, instances of that 
  %%    attribute must match the default value.
  %%  
  %%  [VC: Notation Declared]                       [76]
  %%
  %%    The Name must match the declared name of a notation.
  %%
  %%  [VC: Unique Notation Name]                    [82]
  %%  
  %%    Only one notation declaration can declare a given Name.
  %%  
  %%  [VC: Element Valid]                           [39]
  %%
  %%    An element is valid if there is a declaration matching elementdecl where the Name matches the 
  %%    element type, and one of the following holds:
  %%    
  %%      1.  The declaration matches EMPTY and the element has no content.
  %%    
  %%      2.  The declaration matches children and the sequence of child elements belongs to the 
  %%          language generated by the regular expression in the content model, with optional white 
  %%          space (characters matching the nonterminal S) between the start-tag and the first child
  %%          element, between child elements, or between the last child element and the end-tag.
  %%          Note that a CDATA section containing only white space does not match the nonterminal S, 
  %%          and hence cannot appear in these positions.
  %%    
  %%      3.  The declaration matches Mixed and the content consists of character data and child 
  %%          elements whose types match names in the content model.
  %%    
  %%      4.  The declaration matches ANY, and the types of any child elements have been declared.
  %% 
  %%  [VC: Attribute Value Type]                    [41]
  %%
  %%    The attribute must have been declared; the value must be of the type declared for it. 
  %%    (For attribute types, see 3.3 Attribute-List Declarations.)
  %%  
  %%  [VC: Entity Declared]                         [68]  [69]     -- entity_declared?
  %%  
  %%    In a document with an external subset or external parameter entities with "standalone='no'", 
  %%    the Name given in the entity reference must match that in an entity declaration. 
  %% 
  %%    For interoperability, valid documents should declare the entities amp, lt, gt, apos, quot, in 
  %%    the form specified in 4.6 Predefined Entities. The declaration of a parameter entity must 
  %%    precede any reference to it. Similarly, the declaration of a general entity must precede any 
  %%    attribute-list declaration containing a default value with a direct or indirect reference to 
  %%    that general entity.
  %%
  %% -------------------------------------------------------------------------------------------------

endspec


