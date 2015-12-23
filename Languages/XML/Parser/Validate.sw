(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

XML qualifying spec

  import ../XML_Sig

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
  %%%   Accordingly, we introduce Kestrel specific productions, labelled [K1] .. [K40]
  %%%   which are implemented here to factor some original W3 ruls into a parsing
  %%%   stage using KI rules followed by post-parsing well-formedness checks based
  %%%   perhaps on other W3 rules.
  %%%
  %%%   All such substitutions are clearly indicated, and the required well-formedness
  %%%   checks are indicated by KWFC and KVC annotations, analogous to WFC and VC annotations.
  %%%
  %%%   Original W3 rules that have been replaced by KI rules are flagged with an asterisk.
  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XML Document                                                                        %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: A data object is an XML document if it is well-formed, as defined in this (W3)
  %%   specification. A well-formed XML document may in addition be valid if it meets certain further
  %%   constraints.]
  %%
  %%  The following English text is at http://www.w3.org/TR/REC-xml#sec-physical-struct :
  %%
  %%  4 Physical Structures
  %%
  %%  [Definition: An XML document may consist of one or many storage units.
  %%   These are called entities; they all have content and are all (except for the document entity
  %%   and the external DTD subset) identified by entity name.]
  %%
  %%  Each XML document has one entity called the document entity, which serves as the starting
  %%  point for the XML processor and may contain the whole document.
  %%
  %%  Entities may be either parsed or unparsed.
  %%
  %%  [Definition: A parsed entity's contents are referred to as its replacement text; this text is
  %%   considered an integral part of the document.]
  %%
  %%  [Definition: A parsed entity contains text, a sequence of characters, which may represent
  %%   markup or character data.]
  %%
  %%  [Definition: An unparsed entity is a resource whose contents may or may not be text, and if
  %%   text, may be other than XML. Each unparsed entity has an associated notation, identified by
  %%   name. Beyond a requirement that an XML processor make the identifiers for the entity and
  %%   notation available to the application, XML places no constraints on the contents of unparsed
  %%   entities.]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Document entity                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  4.3.2 Well-Formed Parsed Entities:
  %%
  %%  The document entity is well-formed if it matches the production labeled 'document'.
  %%
  %%  [Definition: The document entity serves as the root of the entity tree and a starting-point
  %%   for an XML processor.]
  %%
  %%  This [W3] specification does not specify how the document entity is to be located by an XML
  %%  processor; unlike other entities, the document entity has no name and might well appear on
  %%  a processor input stream without any identification at all.
  %%
  %%  [Definition: XML documents should begin with an XML declaration which specifies the version
  %%   of XML being used.]
  %%
  %%  [Definition: There is exactly one element, called the root, or document element, no part of
  %%   which appears in the content of any other element.]
  %%
  %%  For all other elements, if the start-tag is in the content of another element, the end-tag
  %%  is in the content of the same element. More simply stated, the elements, delimited by start-
  %%  and end-tags, nest properly within each other.
  %%
  %%  [Definition: As a consequence of this, for each non-root element C in the document, there is
  %%   one other element P in the document such that C is in the content of P, but is not in the
  %%   content of any other element that is in the content of P. P is referred to as the parent of C,
  %%   and C as a child of P.]
  %%
  %%  *[1]  document  ::=  prolog element Misc*
  %% *[22]  prolog    ::=  XMLDecl? Misc* (doctypedecl  Misc*)?
  %%
  %%   ==>
  %%
  %%  [K1]  document  ::=  XMLDecl? MiscList doctypedecl? MiscList element MiscList
  %%
  %%                                                             [VC:   Root Element Type]
  %%                                                             [KVC:  Valid DTD]
  %%                                                             [KVC:  Valid Root Element]
  %%                                                             [KVC:  Element Valid]
  %%
  %%  [K2]  MiscList  ::=  Misc*
  %%
  %%  [27]  Misc      ::=  Comment | PI | S
  %%
  %%  [Definition: Markup takes the form of start-tags, end-tags, empty-element tags, entity
  %%   references, character references, comments, CDATA section delimiters, document type
  %%   declarations, processing instructions, XML declarations, text declarations, and any white
  %%   space that is at the top level of the document entity (that is, outside the document
  %%   element and not inside any other markup).]
  %%
  %%  [Definition: All text that is not markup constitutes the character data of the document.]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% We provide a special type for Valid_XML_Document, but not ValidDTD, ValidElement, etc.
  %% The assumption is that a valid xml document is recursively composed of valid components.

  type Valid_XML_Document = (XML_Document | valid_xml_document?)

  %%
  %%  [K1] *[1] -- [KVC: Valid DTD]
  %%               [VC: Root Element Type]
  %%               [KVC: Valid Root Element]
  %%               [KVC: External General Parsed Entity]
  %%
  def valid_xml_document? (xml_doc : XML_Document) : Bool =
      (valid_dtd?                    xml_doc)  % must validate combined internal/external dtd
    & (consistent_root_element_type? xml_doc)
    & (valid_root_element?           xml_doc)
    & (all valid_external_general_parsed_entity? xml_doc.entities)


  %%  A complication of XML is that the document type declaration (DTD) is
  %%  divided into internal and external subsets.  The internal dtd lives
  %%  within the top-level document entity, but the external subset is its
  %%  own top-level entity.

  %%
  %%  [KVC: Valid DTD]                              [K1] *[1] -- valid_dtd?
  %%
  %%    A document must contain exactly one doctypedecl.
  %%
  def valid_dtd? (xml_doc : XML_Document) : Bool =
    let items = xml_doc.document in
    %% We've already determined there is at most one dtd, for the document to be well-formed,
    %% so we only need to test here for at least one dtd.
    foldl (fn (item, saw_dtd?) ->
	   case item of
	     | DTD _ -> true
	     | _     -> saw_dtd?)
          false
	  items

  %%
  %%  [VC: Root Element Type]                       [K1] [K16] *[28] -- consistent_root_element_type?
  %%
  %%    The Name in the document type declaration must match the element type of the root element.
  %%
  def consistent_root_element_type? (xml_document : XML_Document) : Bool =
   let items = xml_document.document in
   case (foldl (fn (item, (root_name : Option ElementName, dtd_name)) ->
		case item of
		  | DTD  dtd -> (root_name, Some dtd.name)
		  | Element (root : Element) -> (Some (element_name root), dtd_name)
		  | _ -> (root_name, dtd_name))
	       (None, None)
	       items)
    of
     | (Some root_name, Some dtd_name) -> true % root_name = dtd_name
     | _ -> false

  %%
  %%  [KVC: Valid Root Element]                     [K1] -- valid_root_element?
  %%
  %%    In a valid document, every element must be valid.
  %%
  def valid_root_element? (xml_document : XML_Document) : Bool =
   let items = xml_document.document in
    let dtd_and_root = foldl (fn (item, (dtd, root)) ->
			      case item of
				| DTD     dtd  -> (Some dtd, root)
				| Element root -> (dtd, Some root)
				| _ -> (dtd, root))
                             (None, None)
			     items
    in
      case dtd_and_root of
	| (Some dtd, Some root) -> valid_element? (root, dtd)
	| _ -> false

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          ElementTag                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Rules [K4] -- [K9] simplify the parsing (and especially any associated error reporting) for
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
  %%  [K4]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix
  %%  [K5]  ElementTagPrefix   ::=  ( '?' | '/'  | '' )
  %%  [K6]  ElementName        ::=  NmToken
  %%  [K7]  ElementAttributes  ::=  List ElementAttribute
  %%  [K8]  ElementAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%  [K9]  ElementTagPostfix  ::=  ( '?' | '/'  | '' )
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          PI                                                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  *[16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'
  %%    ==>
  %%  [K10]  PI        ::= '<?' PITarget (S PIValue)? '?>'
  %%  [K11]  PIValue   ::= Char* - (Char* '?>' Char*)
  %%
  %%   [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          External                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Well-formedness constraint: External Subset
  %%
  %%   "The external subset, if any, must match the production for 'extSubset'."
  %%
  %% -------------------------------------------------------------------------------------------------
  %%
  %%  *[30]  extSubset           ::=  TextDecl? extSubsetDecl
  %%  *[31]  extSubsetDecl       ::=  ( markupdecl | conditionalSect | DeclSep)*
  %%     =>
  %%  [K12]  extSubset           ::=  ( extSubsetDecl )*
  %%                                                             [KWFC: One TextDecl]
  %%                                                             [WFC: In DTD]
  %%                                                             [VC: Unique Element Type Declaration]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: One Notation Per Element Type]
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %%  [K13]  extSubsetDecl       ::=  TextDecl | elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | includeSect | ignoreSect | S
  %%
  %%  *[61]  conditionalSect     ::=  includeSect | ignoreSect
  %%
  %%   [62]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' extSubsetDecl ']]>'
  %%
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %%
  %%   [63]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents* ']]>'
  %%
  %%                                                             [VC: Proper Conditional Section/PE Nesting]
  %%
  %%   [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %%
  %%   [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %%
  %%  *[77]  TextDecl            ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %%    ==>
  %%  [K14]  TextDecl            ::=  ElementTag
  %%
  %%                                                             [KWFC: Text Decl]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%  [VC: Unique Element Type Declaration]         [K12] [45]
  %%
  %%    No element type may be declared more than once.
  %%
  def unique_element_type_declarations? (dtd             : DocTypeDecl,
					 external_subset : ExtSubset)
    : Bool =
    %% This is O(N**2) and could be smarter, but that's not worth it unless
    %% there's an implausibly huge DTD (tens of thousands of element decls).
    let decls = external_subset in
    let
      def probe (decls, names_seen) =
	case decls of
	  | [] -> true

	  | (Element decl) :: tail ->
	    let name = decl.name in
	    if member (name, names_seen) then
	      false
	    else
	      probe (tail, cons (name, names_seen))
	  | _ :: tail ->
	    probe (tail, names_seen)
    in
      probe (decls, [])

  %%  [VC: One ID per Element Type]                 [K12] [K24] *[56]
  %%
  %%    No element type may have more than one ID attribute specified.
  %%
  def one_id_per_element_type? (dtd             : DocTypeDecl,
				external_subset : ExtSubset)
    : Bool =
    %% This is O(N**2) and could be smarter, but that's not worth it unless
    %% there's an implausibly huge DTD (tens of thousands of attlist decls).
    let decls = external_subset in
    let
      def probe (decls, names_seen) =
	case decls of
	  | [] -> true

	  | (Attributes decl) :: tail ->
	    let name_of_element_type = decl.name in
	    if member (name_of_element_type, names_seen) then
	      false
	    else
	      probe (tail, cons (name_of_element_type, names_seen))
	  | _ :: tail ->
	    probe (tail, names_seen)
    in
      probe (decls, [])

  %%
  %%  [VC: One Notation Per Element Type]           [K12] [58]
  %%
  %%    No element type may have more than one NOTATION attribute specified.
  %%

  %%
  %%  [VC: No Notation on Empty Element]            [K12] [58]
  %%
  %%    For compatibility, an attribute of type NOTATION must not be declared on an element declared
  %%    EMPTY.
  %%

  %%  [VC: Proper Group/PE Nesting]                 [K21] [K22] *[49] *[50] [51]
  %%
  %%  TODO -- Test during expansion
  %%

  %%  [VC: Proper Conditional Section/PE Nesting]   [62]  [63]
  %%
  %%    If any of the "<![", "[", or "]]>" of a conditional section is contained in the replacement
  %%    text for a parameter-entity reference, all of them must be contained in the same replacement
  %%     text.
  %%
  %%  TODO -- test during expansion
  %%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          extParsedEnt                                                                        %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  4.3.2 Well-Formed Parsed Entities:
  %%
  %%  "An external general parsed entity is well-formed if it matches the production labeled
  %%   'extParsedEnt'."
  %%
  %%   [78]  extParsedEnt        ::=  TextDecl? content
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%
  %%  [KVC: External General Parsed Entity]         Specification in English in section 4.3.2
  %%
  op valid_external_general_parsed_entity? : ExtParsedEnt     -> Bool

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XMLDecl                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  *[23]  XMLDecl       ::=  '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
  %%    ==>
  %%  [K15]  XMLDecl       ::=  ElementTag
  %%
  %%                                                             [KWFC: XML Decl]
  %%
  %%  *[24]  VersionInfo   ::=  S 'version' Eq ("'" VersionNum "'" | '"' VersionNum '"')
  %%
  %%  *[25]  Eq            ::=  S? '=' S?
  %%
  %%  *[26]  VersionNum    ::=  ([a-zA-Z0-9_.:] | '-')+
  %%
  %%  *[32]  SDDecl        ::=  S 'standalone' Eq (("'" ('yes' | 'no') "'") | ('"' ('yes' | 'no') '"'))
  %%
  %%                                                             [VC: Standalone Document Declaration]
  %%
  %%  *[80]  EncodingDecl  ::=  S 'encoding' Eq ('"' EncName '"' | "'" EncName "'" )
  %%
  %%  *[81]  EncName       ::=  [A-Za-z] ([A-Za-z0-9._] | '-')*
  %%                            /* Encoding name contains only Latin characters */
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%  [VC: Standalone Document Declaration] -- [K15] *[32]
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
  %% TODO -- misc validity checks
  %%

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
  %%  *[28]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>'
  %%
  %%                                                            *[VC:  Root Element Type]
  %%                                                            *[WFC: External Subset]
  %%
  %% *[28a]  DeclSep      ::=  PEReference | S
  %%                                                            *[WFC: PE Between Declarations]
  %%
  %%  *[29]  markupdecl   ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment
  %%
  %%                                                            *[VC:  Proper Declaration/PE Nesting]
  %%                                                            *[WFC: PEs in Internal Subset]
  %%    ==>
  %%  [K16]  doctypedecl  ::=  '<!DOCTYPE' S Name (S ExternalID)? S? DTD_Decls? '>'
  %%
  %%                                                             [WFC: External Subset]
  %%                                                             [VC:  Root Element Type]
  %%                                                             [WFC: PE Between Declarations]
  %%                                                             [VC:  Proper Declaration/PE Nesting]
  %%
  %%  [K17]  DTD_Decls    ::=  '[' (DTD_Decl)* ']' S?
  %%  [K18]  DTD_Decl     ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S
  %%
  %%                                                             [WFC: PEs in Internal Subset]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%  [VC: Root Element Type]                       [K1] [K16] *[28] -- consistent_root_element_type?

  %%  [VC: Proper Declaration/PE Nesting]           [K16] *[29]
  %%
  %%    Parameter-entity replacement text must be properly nested with markup declarations.
  %%
  %%    That is to say, if either the first character or the last character of a markup declaration
  %%    (markupdecl above) is contained in the replacement text for a parameter-entity reference,
  %%    both must be contained in the same replacement text.
  %%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD ElementDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>'
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %%   [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children
  %%
  %%  *[47]  children     ::=  (choice | seq) ('?' | '*' | '+')?
  %%    ==>
  %%  [K19]  children     ::=  cp
  %%
  %%                                                             [KWFC: Children Decl]
  %%
  %%  *[48]  cp           ::=  (Name | choice | seq) ('?' | '*' | '+')?
  %%    ==>
  %%  [K20]  cp           ::=  cpbody ('?' | '*' | '+')?
  %%  [K21]  cpbody       ::=  Name | choice | seq
  %%
  %%  *[49]  choice       ::=  '(' S? cp ( S? '|' S? cp )+ S? ')'
  %%    ==>
  %%  [K22]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')'
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%  *[50]  seq          ::=  '(' S? cp ( S? ',' S? cp )* S? ')'
  %%    ==>
  %%  [K23]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')'
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%   [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')'
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%                                                             [VC: No Duplicate Types]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%  [VC: Unique Element Type Declaration]         [K12] [45]

  %%  [VC: Proper Group/PE Nesting]                 [K22] [K23] *[49] *[50] [51]
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

  %%
  %%  [VC: No Duplicate Types]                      [51]
  %%
  %%    The same name must not appear more than once in a single mixed-content declaration.
  %%
  def valid_mixed? (mixed : Mixed) : Bool =
    case mixed of
      | Names {w1, names, w2} ->
        let
	   def probe (tail, names_seen) =
	     case tail of
	       | [] -> true
	       | name :: tail ->
	         if member (name, names_seen) then
		   false
		 else
		   probe (tail, cons (name, names_seen))
	in
	  probe (names, [])
      | _ -> true

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD AttListDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
  %%
  %%   [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %%                                                             [VC: ID Attribute Default] (implicit)
  %%
  %%  *[54]  AttType         ::=  StringType | TokenizedType | EnumeratedType
  %%  *[55]  StringType      ::=  'CDATA'
  %%  *[56]  TokenizedType   ::=  'ID'                          *[VC: ID]
  %%                                                            *[VC: One ID per Element Type]
  %%                                                            *[VC: ID Attribute Default]
  %%                            | 'IDREF'                       *[VC: IDREF]
  %%                            | 'IDREFS'                      *[VC: IDREF]
  %%                            | 'ENTITY'                      *[VC: Entity Name]
  %%                            | 'ENTITIES'                    *[VC: Entity Name]
  %%                            | 'NMTOKEN'                     *[VC: Name Token]
  %%                            | 'NMTOKENS'                    *[VC: Name Token]
  %%  *[57]  EnumeratedType  ::=  NotationType | Enumeration
  %%    ==>
  %%  [K24]  AttType         ::=  'CDATA'
  %%                            | 'ID'                           [VC: ID]
  %%                                                             [VC: One ID per Element Type]
  %%                                                             [VC: ID Attribute Default]
  %%                            | 'IDREF'                        [VC: IDREF]
  %%                            | 'IDREFS'                       [VC: IDREF]
  %%                            | 'ENTITY'                       [VC: Entity Name]
  %%                            | 'ENTITIES'                     [VC: Entity Name]
  %%                            | 'NMTOKEN'                      [VC: Name Token]
  %%                            | 'NMTOKENS'                     [VC: Name Token]
  %%                            | NotationType
  %%                            | Enumeration
  %%
  %%   [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')'
  %%
  %%                                                             [VC: Notation Attributes]
  %%                                                             [VC: One Notation Per Element Type]
  %%                                                             [VC: No Notation on Empty Element]
  %%
  %%   [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')'
  %%
  %%                                                             [VC: Enumeration]
  %%
  %%   [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue)
  %%
  %%                                                             [VC:  Required Attribute]
  %%                                                             [VC:  Attribute Default Legal]
  %%                                                             [WFC: No < in Attribute Values]
  %%                                                             [VC:  Fixed Attribute Default]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%
  %%  [VC: ID Attribute Default]                    [53] [K24] *[56]
  %%
  %%    An ID attribute must have a declared default of #IMPLIED or #REQUIRED.
  %%

  %%
  %%  [VC: Attribute Default Legal]                 [60]
  %%
  %%    The declared default value must meet the lexical constraints of the declared attribute type.
  %%

  %%  [VC: ID]                                      [K24] *[56]
  %%
  %%    Values of type ID must match the Name production. A name must not appear more than once in an
  %%    XML document as a value of this type; i.e., ID values must uniquely identify the elements
  %%    which bear them.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%  [VC: One ID per Element Type]                 [K12] [K24] *[56]

  %%
  %%  [VC: IDREF]                                   [K24] *[56]
  %%
  %%    Values of type IDREF must match the Name production, and values of type IDREFS must match
  %%    Names; each Name must match the value of an ID attribute on some element in the XML document;
  %%     i.e. IDREF values must match the value of some ID attribute.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%
  %%  [VC: Entity Name]                             [K24] *[56]
  %%
  %%    Values of type ENTITY must match the Name production, values of type ENTITIES must match
  %%    Names; each Name must match the name of an unparsed entity declared in the DTD.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%
  %%  [VC: Name Token]                              [K24] *[56]
  %%
  %%    Values of type NMTOKEN must match the Nmtoken production; values of type NMTOKENS must match
  %%    Nmtokens.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%  [VC: Notation Attributes]                     [58]
  %%
  %%    Values of this type must match one of the notation names included in the declaration;
  %%    all notation names in the declaration must be declared.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%  [VC: One Notation Per Element Type]           [K12] [58]
  %%
  %%  TODO -- Validity Check

  %%  [VC: No Notation on Empty Element]            [K12] [58]
  %%
  %%  TODO -- Validity Check

  %%
  %%  [VC: Enumeration]                             [59]
  %%
  %%    Values of this type must match one of the Nmtoken tokens in the declaration.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%  [VC: Attribute Default Legal]                 [53] [60]

  %%
  %%  [VC: Fixed Attribute Default]                 [60]
  %%
  %%    If an attribute has a default value declared with the #FIXED keyword, instances of that
  %%    attribute must match the default value.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%  [VC: Required Attribute]                      [60]
  %%
  %%    If the default declaration is the keyword #REQUIRED, then the attribute must be specified for
  %%    all elements of the type in the attribute-list declaration.
  %%
  %%  TODO -- Expansion Rule
  %%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD EntityDecl                                                                      %%%
  %%%          DTD NotationDecl                                                                    %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [70]  EntityDecl     ::=  GEDecl | PEDecl
  %%
  %%   [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %%
  %%   [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %%
  %%   [73]  EntityDef      ::=  EntityValue | (ExternalID NDataDecl?)
  %%
  %%   [74]  PEDef          ::=  EntityValue | ExternalID
  %%
  %%   [76]  NDataDecl      ::=  S 'NDATA' S Name
  %%
  %%                                                             [VC: Notation Declared]
  %%
  %% ------------------------------------------------------------------------------------------------
  %%
  %%  *[82]  NotationDecl   ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>'
  %%    ==>
  %%  [K25]  NotationDecl   ::=  '<!NOTATION' S Name S GenericID S? '>'
  %%
  %%                                                             [VC: Unique Notation Name]
  %%
  %% ------------------------------------------------------------------------------------------------
  %%
  %%  *[75]  ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral
  %%    ==>
  %%  [K26]  ExternalID     ::=  GenericID
  %%
  %%                                                             [KWFC: External ID]
  %%
  %%  *[83]  PublicID       ::=  'PUBLIC' S PubidLiteral
  %%    ==>
  %%  [K27]  PublicID       ::=  GenericID
  %%
  %%                                                             [KWFC: Public ID]
  %%
  %%  [K28]  GenericID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral (S SystemLiteral)?
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%  [VC: Notation Declared]                       [76]
  %%
  %%    The Name must match the declared name of a notation.
  %%
  %%  TODO -- Search through <!NOTATION decls, both internal and external subset
  %%

  %%  [VC: Unique Notation Name]                    [K25] *[82]
  %%
  %%    Only one notation declaration can declare a given Name.
  %%
  %%  TODO -- check both internal and external subsets
  %%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Element                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [39]  element  ::=  EmptyElemTag | STag content ETag
  %%
  %%                                                             [WFC: Element Type Match]
  %%                                                             [VC:  Element Valid]
  %%
  %%  *[40]  STag          ::=  '<' Name (S Attribute)* S? '>'
  %%
  %%                                                            *[WFC: Unique Att Spec]
  %%    ==>
  %%  [K29]  STag          ::=  ElementTag
  %%
  %%                                                             [KWFC: Start Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%
  %%  *[41]  Attribute     ::=  Name Eq AttValue
  %%    ==>
  %%   [K8]  ElementAttribute   ::=  S NmToken S? '=' S? QuotedText
  %%
  %%                                                             [VC:  Attribute Value Type]
  %%                                                             [WFC: No External Entity References]
  %%                                                             [WFC: No < in Attribute Values]
  %%
  %%  *[42]  ETag          ::=  '</' Name S? '>'
  %%    ==>
  %%  [K30]  ETag          ::=  ElementTag
  %%
  %%                                                             [KWFC: End Tag]
  %%
  %%  Since the chardata in *[43] is typically used for indentation,
  %%  it makes more sense to group it as in [K18]:
  %%
  %%  *[43]  content       ::=  CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
  %%    ==>
  %%  [K31]  content       ::=  content_item* CharData?
  %%  [K32]  content_item  ::=  CharData? (element | Reference | CDSect | PI | Comment
  %%
  %%  *[44]  EmptyElemTag  ::=  '<' Name (S Attribute)* S? '/>' 60]
  %%
  %%                                                             [WFC: Unique Att Spec]
  %%    ==>
  %%  [K33]  EmptyElemTag  ::=  ElementTag
  %%
  %%                                                             [KWFC: Empty Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%  [VC: Attribute Value Type]                    [K8] *[41]
  %%
  %%    The attribute must have been declared; the value must be of the type declared for it.
  %%    (For attribute types, see 3.3 Attribute-List Declarations.)
  %%
  %%  TODO -- Check against DTD
  %%

  %%  [VC:  Element Valid]                          [K1] [39]
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
  %%  [KVC: Element Valid]                          [K1] [39]
  %%
  %%      Every child element of a valid element is valid.
  %%
  def valid_element? (element : Element, dtd : DocTypeDecl) : Bool =
    let name = element_name element in
    case element of
      | Empty _ -> true
      | Full possible_element ->
        let content = possible_element.content in
	let items   = content.items   in
	(all (fn item -> case item of
			   | (_, Element element) -> valid_element? (element, dtd)
	                   %% todo: expand references, etc.
			   | _ -> true)
             items)
	&
	(case find_matching_element_decl (name, dtd) of
	   | None      -> false
	   | Some edecl ->
	     case edecl.contents of
	       | Empty ->
	         %%
	         %%      1.  The declaration matches EMPTY and the element has no content.
	         %%
	         (case element of
		      | Empty _ -> true
		        | Full element -> (case (items, content.trailer) of
					       | ([], None) -> true
					       %% todo: what if the content and/or tariler is just whitespace, etc.
					         | _ -> false))

	       | Children children ->
		 %%
		 %%      2.  The declaration matches children and the sequence of child elements belongs to the
		 %%          language generated by the regular expression in the content model, with optional white
		 %%          space (characters matching the nonterminal S) between the start-tag and the first child
		 %%          element, between child elements, or between the last child element and the end-tag.
		 %%          Note that a CDATA section containing only white space does not match the nonterminal S,
		 %%          and hence cannot appear in these positions.
		 %% Todo
		 true

	       | Mixed    mixed    ->
		 %%
		 %%      3.  The declaration matches Mixed and the content consists of character data and child
		 %%          elements whose types match names in the content model.
		 %%
		 let declared_names  = (case mixed of
					  | NoNames _  -> []
					  | Names   xx -> xx.names)
		 in
		   (all (fn item -> case item of
				      | (_, Element element) -> exists (fn (_,_,candidate_name) -> name = candidate_name) declared_names
				      | _ -> false)
		        items)

	       | Any ->
		 %%      4.  The declaration matches ANY, and the types of any child elements have been declared.
		    true % (already tested above)
		   )

  def find_matching_element_decl (name : ElementName, dtd : DocTypeDecl) : Option ElementDecl =
    case dtd.decls of
      | None -> None
      | Some dtd_decls ->
        case (find (fn decl -> (case decl of
				  | Element edecl -> name = edecl.name
				  | _ -> false))
	           dtd_decls.decls)
	  of None -> None
	   | Some (Element edecl) -> Some edecl

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Character_Strings                                                                   %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [3]  S         ::=  (#x20 | #x9 | #xD | #xA)+
  %%
  %%  [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %%
  %%  [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %%
  %%  [18]  CDSect    ::=  CDStart CData CDEnd
  %%  [19]  CDStart   ::=  '<![CDATA['
  %%  [20]  CData     ::=  (Char* - (Char* ']]>' Char*))
  %%  [21]  CDEnd     ::=  ']]>'
  %%
  %%  Note that the anonymous rule about characters (see section below on WFC's) implicitly
  %%  restricts the characters that may appear in CharData to be Char's.
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Literals                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%    [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %%   [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %%                                                             [WFC: No < in Attribute Values] (implicit)
  %%
  %%  *[11]  SystemLiteral   ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %%    ==>
  %%  [K34]  SystemuLiteral  ::=  QuotedText
  %%
  %%  *[12]  PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'"
  %%    ==>
  %%  [K35]  PubidLiteral    ::=  QuotedText
  %%
  %%                                                             [KWFC: Pubid Literal]
  %%
  %%   [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %%  [K36]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          References                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';'
  %%
  %%                                                             [WFC: Legal Character]
  %%
  %%  [67]  Reference    ::=  EntityRef | CharRef
  %%
  %%  [68]  EntityRef    ::=  '&' Name ';'
  %%
  %%                                                             [WFC: Entity Declared]
  %%                                                             [WFC: Parsed Entity]
  %%                                                             [WFC: No Recursion]
  %%                                                             [VC:  Entity Declared]
  %%
  %%  [69]  PEReference  ::=  '%' Name ';'
  %%
  %%                                                             [WFC: In DTD]
  %%                                                             [WFC: No Recursion]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [VC:  Proper Group/PE Nesting] (implicit)
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Chars                                                                               %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [2]  Char          ::=  #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
  %%                           /* any Unicode character, excluding the surrogate blocks, FFFE, and FFFF. */
  %%
  %%  [84]  Letter        ::=  BaseChar | Ideographic
  %%
  %%  [85]  BaseChar      ::=  [#x0041-#x005A] | [#x0061-#x007A] |   /* ascii: [A-Z] [a-z] */
  %%                            /* annotated vowels (umlaut, circumflex, ...) */
  %%                           [#x00C0-#x00D6] | [#x00D8-#x00F6] | [#x00F8-#x00FF] |
  %%                            /* lots of odd characters */
  %%                           [#x0100-#x0131] | [#x0134-#x013E] | [#x0141-#x0148] |
  %%                           [#x014A-#x017E] | [#x0180-#x01C3] | [#x01CD-#x01F0] | [#x01F4-#x01F5] |
  %%                           [#x01FA-#x0217] | [#x0250-#x02A8] | [#x02BB-#x02C1] | #x0386 |
  %%                           [#x0388-#x038A] | #x038C | [#x038E-#x03A1] | [#x03A3-#x03CE] |
  %%                           [#x03D0-#x03D6] | #x03DA | #x03DC | #x03DE | #x03E0 | [#x03E2-#x03F3] |
  %%                           [#x0401-#x040C] | [#x040E-#x044F] | [#x0451-#x045C] | [#x045E-#x0481] |
  %%                           [#x0490-#x04C4] | [#x04C7-#x04C8] | [#x04CB-#x04CC] | [#x04D0-#x04EB] |
  %%                           [#x04EE-#x04F5] | [#x04F8-#x04F9] | [#x0531-#x0556] | #x0559 |
  %%                           [#x0561-#x0586] | [#x05D0-#x05EA] | [#x05F0-#x05F2] | [#x0621-#x063A] |
  %%                           [#x0641-#x064A] | [#x0671-#x06B7] | [#x06BA-#x06BE] | [#x06C0-#x06CE] |
  %%                           [#x06D0-#x06D3] | #x06D5 | [#x06E5-#x06E6] | [#x0905-#x0939] | #x093D |
  %%                           [#x0958-#x0961] | [#x0985-#x098C] | [#x098F-#x0990] | [#x0993-#x09A8] |
  %%                           [#x09AA-#x09B0] | #x09B2 | [#x09B6-#x09B9] | [#x09DC-#x09DD] |
  %%                           [#x09DF-#x09E1] | [#x09F0-#x09F1] | [#x0A05-#x0A0A] | [#x0A0F-#x0A10] |
  %%                           [#x0A13-#x0A28] | [#x0A2A-#x0A30] | [#x0A32-#x0A33] | [#x0A35-#x0A36] |
  %%                           [#x0A38-#x0A39] | [#x0A59-#x0A5C] | #x0A5E | [#x0A72-#x0A74] |
  %%                           [#x0A85-#x0A8B] | #x0A8D | [#x0A8F-#x0A91] | [#x0A93-#x0AA8] |
  %%                           [#x0AAA-#x0AB0] | [#x0AB2-#x0AB3] | [#x0AB5-#x0AB9] | #x0ABD | #x0AE0 |
  %%                           [#x0B05-#x0B0C] | [#x0B0F-#x0B10] | [#x0B13-#x0B28] | [#x0B2A-#x0B30] |
  %%                           [#x0B32-#x0B33] | [#x0B36-#x0B39] | #x0B3D | [#x0B5C-#x0B5D] |
  %%                           [#x0B5F-#x0B61] | [#x0B85-#x0B8A] | [#x0B8E-#x0B90] | [#x0B92-#x0B95] |
  %%                           [#x0B99-#x0B9A] | #x0B9C | [#x0B9E-#x0B9F] | [#x0BA3-#x0BA4] |
  %%                           [#x0BA8-#x0BAA] | [#x0BAE-#x0BB5] | [#x0BB7-#x0BB9] | [#x0C05-#x0C0C] |
  %%                           [#x0C0E-#x0C10] | [#x0C12-#x0C28] | [#x0C2A-#x0C33] | [#x0C35-#x0C39] |
  %%                           [#x0C60-#x0C61] | [#x0C85-#x0C8C] | [#x0C8E-#x0C90] | [#x0C92-#x0CA8] |
  %%                           [#x0CAA-#x0CB3] | [#x0CB5-#x0CB9] | #x0CDE | [#x0CE0-#x0CE1] |
  %%                           [#x0D05-#x0D0C] | [#x0D0E-#x0D10] | [#x0D12-#x0D28] | [#x0D2A-#x0D39] |
  %%                           [#x0D60-#x0D61] | [#x0E01-#x0E2E] | #x0E30 | [#x0E32-#x0E33] |
  %%                           [#x0E40-#x0E45] | [#x0E81-#x0E82] | #x0E84 | [#x0E87-#x0E88] | #x0E8A |
  %%                           #x0E8D | [#x0E94-#x0E97] | [#x0E99-#x0E9F] | [#x0EA1-#x0EA3] | #x0EA5 |
  %%                           #x0EA7 | [#x0EAA-#x0EAB] | [#x0EAD-#x0EAE] | #x0EB0 | [#x0EB2-#x0EB3] |
  %%                           #x0EBD | [#x0EC0-#x0EC4] | [#x0F40-#x0F47] | [#x0F49-#x0F69] |
  %%                           [#x10A0-#x10C5] | [#x10D0-#x10F6] | #x1100 | [#x1102-#x1103] |
  %%                           [#x1105-#x1107] | #x1109 | [#x110B-#x110C] | [#x110E-#x1112] | #x113C |
  %%                           #x113E | #x1140 | #x114C | #x114E | #x1150 | [#x1154-#x1155] | #x1159 |
  %%                           [#x115F-#x1161] | #x1163 | #x1165 | #x1167 | #x1169 | [#x116D-#x116E] |
  %%                           [#x1172-#x1173] | #x1175 | #x119E | #x11A8 | #x11AB | [#x11AE-#x11AF] |
  %%                           [#x11B7-#x11B8] | #x11BA | [#x11BC-#x11C2] | #x11EB | #x11F0 | #x11F9 |
  %%                           [#x1E00-#x1E9B] | [#x1EA0-#x1EF9] | [#x1F00-#x1F15] | [#x1F18-#x1F1D] |
  %%                           [#x1F20-#x1F45] | [#x1F48-#x1F4D] | [#x1F50-#x1F57] | #x1F59 | #x1F5B |
  %%                           #x1F5D | [#x1F5F-#x1F7D] | [#x1F80-#x1FB4] | [#x1FB6-#x1FBC] | #x1FBE |
  %%                           [#x1FC2-#x1FC4] | [#x1FC6-#x1FCC] | [#x1FD0-#x1FD3] | [#x1FD6-#x1FDB] |
  %%                           [#x1FE0-#x1FEC] | [#x1FF2-#x1FF4] | [#x1FF6-#x1FFC] | #x2126 |
  %%                           [#x212A-#x212B] | #x212E | [#x2180-#x2182] | [#x3041-#x3094] |
  %%                           [#x30A1-#x30FA] | [#x3105-#x312C] |
  %%                           [#xAC00-#xD7A3]
  %%
  %%  [86]  Ideographic   ::=  [#x4E00-#x9FA5] | #x3007 | [#x3021-#x3029]
  %%
  %%  [87]  CombiningChar ::=  [#x0300-#x0345] | [#x0360-#x0361] | [#x0483-#x0486] | [#x0591-#x05A1] |
  %%                           [#x05A3-#x05B9] | [#x05BB-#x05BD] | #x05BF | [#x05C1-#x05C2] | #x05C4 |
  %%                           [#x064B-#x0652] | #x0670 | [#x06D6-#x06DC] | [#x06DD-#x06DF] |
  %%                           [#x06E0-#x06E4] | [#x06E7-#x06E8] | [#x06EA-#x06ED] | [#x0901-#x0903] |
  %%                           #x093C | [#x093E-#x094C] | #x094D | [#x0951-#x0954] | [#x0962-#x0963] |
  %%                           [#x0981-#x0983] | #x09BC | #x09BE | #x09BF | [#x09C0-#x09C4] |
  %%                           [#x09C7-#x09C8] | [#x09CB-#x09CD] | #x09D7 | [#x09E2-#x09E3] | #x0A02 |
  %%                           #x0A3C | #x0A3E | #x0A3F | [#x0A40-#x0A42] | [#x0A47-#x0A48] |
  %%                           [#x0A4B-#x0A4D] | [#x0A70-#x0A71] | [#x0A81-#x0A83] | #x0ABC |
  %%                           [#x0ABE-#x0AC5] | [#x0AC7-#x0AC9] | [#x0ACB-#x0ACD] | [#x0B01-#x0B03] |
  %%                           #x0B3C | [#x0B3E-#x0B43] | [#x0B47-#x0B48] | [#x0B4B-#x0B4D] |
  %%                           [#x0B56-#x0B57] | [#x0B82-#x0B83] | [#x0BBE-#x0BC2] | [#x0BC6-#x0BC8] |
  %%                           [#x0BCA-#x0BCD] | #x0BD7 | [#x0C01-#x0C03] | [#x0C3E-#x0C44] |
  %%                           [#x0C46-#x0C48] | [#x0C4A-#x0C4D] | [#x0C55-#x0C56] | [#x0C82-#x0C83] |
  %%                           [#x0CBE-#x0CC4] | [#x0CC6-#x0CC8] | [#x0CCA-#x0CCD] | [#x0CD5-#x0CD6] |
  %%                           [#x0D02-#x0D03] | [#x0D3E-#x0D43] | [#x0D46-#x0D48] | [#x0D4A-#x0D4D] |
  %%                           #x0D57 | #x0E31 | [#x0E34-#x0E3A] | [#x0E47-#x0E4E] | #x0EB1 |
  %%                           [#x0EB4-#x0EB9] | [#x0EBB-#x0EBC] | [#x0EC8-#x0ECD] | [#x0F18-#x0F19] |
  %%                           #x0F35 | #x0F37 | #x0F39 | #x0F3E | #x0F3F | [#x0F71-#x0F84] |
  %%                           [#x0F86-#x0F8B] | [#x0F90-#x0F95] | #x0F97 | [#x0F99-#x0FAD] |
  %%                           [#x0FB1-#x0FB7] | #x0FB9 | [#x20D0-#x20DC] | #x20E1 | [#x302A-#x302F] |
  %%                           #x3099 | #x309A
  %%
  %%  [88]  Digit         ::=  [#x0030-#x0039] |  /* ascii [0-9] */
  %%                           [#x0660-#x0669] | [#x06F0-#x06F9] | [#x0966-#x096F] |
  %%                           [#x09E6-#x09EF] | [#x0A66-#x0A6F] | [#x0AE6-#x0AEF] | [#x0B66-#x0B6F] |
  %%                           [#x0BE7-#x0BEF] | [#x0C66-#x0C6F] | [#x0CE6-#x0CEF] | [#x0D66-#x0D6F] |
  %%                           [#x0E50-#x0E59] | [#x0ED0-#x0ED9] | [#x0F20-#x0F29]
  %%
  %%  [89]  Extender      ::=  #x00B7 | #x02D0 | #x02D1 | #x0387 | #x0640 | #x0E46 | #x0EC6 | #x3005 |
  %%                           [#x3031-#x3035] | [#x309D-#x309E] | [#x30FC-#x30FE]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec


