(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

XML qualifying spec

  import ../Utilities/XML_Base
  import ../Utilities/XML_Unicode
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

  %% -------------------------------------------------------------------------------------------------
  %%  [K1]  document  ::=  XMLDecl? MiscList doctypedecl? MiscList element MiscList
  %% -------------------------------------------------------------------------------------------------

  def print_Document_to_UString (document : Document) : UString =
    (case document.xmldecl of
       | Some decl -> print_XMLDecl decl
       | _ -> [])
    ^ (print_MiscList    document.misc1)
    ^ (print_DocTypeDecl document.dtd)
    ^ (print_MiscList    document.misc2)
    ^ (print_Element     document.element)
    ^ (print_MiscList    document.misc3)

  %% -------------------------------------------------------------------------------------------------
  %%  [K2]  MiscList  ::=  Misc*
  %% -------------------------------------------------------------------------------------------------

  def print_MiscList (items) : UString =
    foldl (fn (result, item) ->  result ^ print_Misc item)
          []
	  items

  %% -------------------------------------------------------------------------------------------------
  %%  [27]  Misc      ::=  Comment | PI | S
  %% -------------------------------------------------------------------------------------------------

  def print_Misc item : UString =
    case item of
      | Comment     comment -> print_Comment     comment
      | PI          pi      -> print_PI          pi
      | WhiteSpace  white   -> print_WhiteSpace  white

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XMLDecl / TextDecl                                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: XML documents should begin with an XML declaration which specifies the version
  %%   of XML being used.]
  %%
  %%  *[23]  XMLDecl       ::=  '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
  %%    ==>
  %%   [K3]  XMLDecl       ::=  ElementTag
  %%                                                             [KWFC: XML Decl]
  %%                                                             [VC: Standalone Document Declaration]
  %%
  %%  TextDecl's appear at the start of external parsed entities:
  %%
  %%  *[77]  TextDecl      ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %%    ==>
  %%   [K4]  TextDecl      ::=  ElementTag
  %%                                                             [KWFC: Text Decl]
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

  %% -------------------------------------------------------------------------------------------------
  %%   [K3]  XMLDecl       ::=  ElementTag
  %%                                                             [KWFC: XML Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: XML Decl]                              [K3] *[23] *[24] *[25] *[26] *[32] *[80] *[81] -- well_formed_xml_decl?
  %%
  %%    XMLDecl  ::=  '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
  %%
  %%    An XMLDecl is just a PI (i.e., tag starting with '<?' and ending with '?>') with target 'xml',
  %%    but having said that, the PI value for an XMLDecl (which is otherwise unstructured in a generic
  %%    PI) is structured as an ElementTag using the syntax for attributes, so it's more convenient
  %%    to treat XMLDecl as a special case of ElementTag (as opposed to being a special case of PI).
  %% -------------------------------------------------------------------------------------------------

  def print_XMLDecl xml = print_ElementTag xml

  %% -------------------------------------------------------------------------------------------------
  %%   [K4]  TextDecl      ::=  ElementTag
  %%                                                             [KWFC: Text Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Text Decl]                             [K4] *[77]  -- well_formed_text_decl?
  %%
  %%    TextDecl  ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %% -------------------------------------------------------------------------------------------------

  def print_TextDecl textdecl = print_ElementTag textdecl

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          ElementTag                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  Rules [K5] -- [K10] simplify the parsing (and especially any associated error reporting) for
  %%  several related constructs given by the W3 grammar as:
  %%
  %%  *[23]  XMLDecl       ::=  '<?xml'     VersionInfo  EncodingDecl? SDDecl?   S? '?>'
  %%  *[77]  TextDecl      ::=  '<?xml'     VersionInfo? EncodingDecl            S? '?>'
  %%  *[40]  STag          ::=  '<'  Name   (S Attribute)*                       S?  '>'
  %%  *[42]  ETag          ::=  '</' Name                                        S?  '>'
  %%  *[41]  Attribute     ::=  Name Eq AttValue
  %%  *[44]  EmptyElemTag  ::=  '<'  Name   (S Attribute)*                       S? '/>'
  %%
  %%  plus several supporting rules for the above
  %%
  %% -------------------------------------------------------------------------------------------------
  %% They are all instances of [K5]:
  %%
  %%  [K5]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix
  %%  [K6]  ElementTagPrefix   ::=  ( '?' | '/'  | '' )
  %%  [K7]  ElementName        ::=  NmToken
  %%  [K8]  ElementAttributes  ::=  List ElementAttribute
  %%  [K9]  ElementAttribute   ::=  S NmToken S? '=' S? AttValue
  %%                                                             [WFC: No External Entity References]
  %%                                                             [VC:  Attribute Value Type]
  %% [K10]  ElementTagPostfix  ::=  ( '?' | '/'  | '' )
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K5]  ElementTag         ::=  ElementTagPrefix ElementName ElementAttributes ElementTagPostfix
  %%  [K6]  ElementTagPrefix   ::=  ( '?' | '/'  | '' )
  %%  [K7]  ElementName        ::=  NmToken
  %% [K10]  ElementTagPostfix  ::=  ( '?' | '/'  | '' )
  %% -------------------------------------------------------------------------------------------------

  def print_ElementTag {prefix, name, attributes, whitespace, postfix} : UString =
   (ustring "<")
   ^ prefix
   ^ (print_NmToken name)
   ^ (print_ElementAttributes attributes)
   ^ (print_WhiteSpace whitespace)
   ^ postfix
   ^ (ustring ">")

  %% -------------------------------------------------------------------------------------------------
  %%  [K8]  ElementAttributes  ::=  List ElementAttribute
  %% -------------------------------------------------------------------------------------------------

  def print_ElementAttributes attributes : UString =
    (foldl (fn (result, attr) -> result ^ print_ElementAttribute attr) [] attributes)

  %% -------------------------------------------------------------------------------------------------
  %%  [K9]  ElementAttribute   ::=  S NmToken S? '=' S? AttValue
  %%                                                             [WFC: No External Entity References]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: No External Entity References]          [K9] *[41] -- no_external_enity_references?
  %%
  %%    Attribute values cannot contain direct or indirect entity references to external entities.
  %%
  %%  Note that "external entity" applies to entity definitions from both the internal and external
  %%  subsets of the DTD.  There are (confusingly) two orthogonal uses of "internal" vs. "external",
  %%  one for internal/external dtd subsets and another for internal/external entities.
  %%
  %%  [Definition: If the entity definition is an EntityValue, the defined entity is called an
  %%   internal entity. ...]
  %%  [Definition: If the entity is not internal, it is an external entity, ...]
  %% -------------------------------------------------------------------------------------------------

  def print_ElementAttribute {w1, name, w2, w3, value} : UString =
    (w1 ^ name ^ w2 ^ (ustring "=") ^ w3 ^ (print_AttValue value))

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          InternalDTD                                                                         %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: The XML document type declaration contains or points to markup declarations that
  %%   provide a grammar for a class of documents. This grammar is known as a document type
  %%   definition, or DTD. The document type declaration can point to an external subset (a special
  %%   kind of external entity) containing markup declarations, or can contain the markup declarations
  %%   directly in an internal subset, or can do both. The DTD for a document consists of both subsets
  %%   taken together.]
  %%
  %%  [Definition: A markup declaration is an element type declaration, an attribute-list declaration,
  %%   an entity declaration, or a notation declaration.]
  %%
  %%  These declarations may be contained in whole or in part within parameter entities, as
  %%  described in the well-formedness and validity constraints below.
  %%
  %%  The internal subset has the following physical form:
  %%
  %%  '<!DOCTYPE' S Name (S ExternalID)? S? DTD_Decls? '>'
  %%
  %%  It may contain the following atomic markup decls:
  %%
  %%   <!ELEMENT    ... >
  %%   <!ATTLIST    ... >
  %%   <!ENTITY     ... >
  %%   <!NOTATATION ... >
  %%
  %%  and/or the following decl separators:
  %%
  %%   <?   target value   ?>  -- PI           (i.e., program instruction)
  %%   <!--     ...       -->  -- Comment
  %%   % Name ;                -- PEReference  (parameter-entity reference)
  %%   space, tab, cr, lf      -- Whitespace
  %%
  %%
  %%  *[28]  doctypedecl    ::=  '<!DOCTYPE' S Name (S ExternalID)? S? ('[' (markupdecl | DeclSep)* ']' S?)? '>'
  %%
  %%                                                            *[WFC: External Subset]
  %%                                                            *[VC:  Root Element Type]
  %%
  %% *[28a]  DeclSep        ::=  PEReference | S
  %%                                                            *[WFC: PE Between Declarations]
  %%
  %%
  %%  *[29]  markupdecl     ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment
  %%
  %%                                                            *[WFC: PEs in Internal Subset]
  %%                                                            *[VC:  Proper Declaration/PE Nesting]
  %%
  %%    ==>
  %%
  %%  [K11]  doctypedecl    ::=  '<!DOCTYPE' S Name (S ExternalID)? S? InternalDecls? '>'
  %%
  %%                                                             [KWFC: External Subset]
  %%                                                             [WFC:  PE Between Declarations]
  %%                                                             [WFC:  PEs in Internal Subset]
  %%                                                             [VC:  Root Element Type]
  %%                                                             [VC:  Proper Declaration/PE Nesting]
  %%
  %%  [K12]  InternalDecls  ::=  '[' InternalDecl* ']' S?
  %%  [K13]  InternalDecl   ::=  Decl
  %%                                                             [KWFC: Internal Decl]
  %%
  %%  [K14]  Decl           ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S | includeSect | ignoreSect
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K11]  doctypedecl    ::=  '<!DOCTYPE' S Name (S ExternalID)? S? InternalDecls? '>'
  %%
  %%                                                             [KWFC: External Subset]
  %%                                                             [WFC:  PE Between Declarations]
  %%                                                             [WFC:  PEs in Internal Subset]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: External Subset]                       [K11] *[28]  -- see parser/printer
  %%
  %%     The external subset, if any, must match the production for ExternalDTD.
  %%
  %%  The parser and printer enforce this restriction.
  %%
  %%  [WFC: PE Between Declarations]                [K11] *[28a] -- see parser/printer
  %%
  %%    The replacement text of a parameter entity reference in a DeclSep must match the production
  %%    extSubsetDecl.
  %%
  %%  The parser and printer enforce this restriction.
  %%
  %%  [WFC: PEs in Internal Subset]                 [K11] *[28] *[28a] *[29] -- no_pe_references_within_internal_markup?
  %%
  %%    In the internal DTD subset, parameter-entity references can occur only where markup
  %%    declarations can occur, not within markup declarations. (This does not apply to references
  %%    that occur in external parameter entities or to the external subset.)
  %% -------------------------------------------------------------------------------------------------

  def print_DocTypeDecl (dtd : DocTypeDecl) : UString =
    case dtd.internal of
      | Some internal -> print_InternalDTD internal
      | _ -> []
    %% Does it make sense to print anything for dtd.external ?

  def print_InternalDTD (internal : InternalDTD) : UString =
    let {w1, name, w2, external_id, w3, decls} = internal in
    w1
    ^ name
    ^ (case w2 of
	 | Some w2 -> w2
	 | _ -> [])
    ^ (case external_id of
	 | Some id -> print_ExternalID id
	 | _ -> [])
    ^ w3
    ^ (print_InternalDecls decls)

  %% -------------------------------------------------------------------------------------------------
  %%  [K12]  InternalDecls    ::=  '[' InternalDecl* ']' S?
  %% -------------------------------------------------------------------------------------------------

  def print_InternalDecls decls : UString =
    case decls of
      | Some {decls, w1} ->
        [91]   % '['
	^ (foldl (fn (result, decl) -> result ^ print_InternalDecl decl) [] decls)
	^ [93] % ']'
	^ w1
      | _ -> []


  %% -------------------------------------------------------------------------------------------------
  %%  [K13]  InternalDecl     ::=  Decl
  %%                                                             [KWFC: Internal Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Internal Decl]                         [K14] *[28] *[28a] *[29] -- internal_decl?
  %%
  %%    InternalDecl ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S
  %% -------------------------------------------------------------------------------------------------

  def print_InternalDecl decl : UString =
    print_Decl decl

  %% -------------------------------------------------------------------------------------------------
  %%  [K14]  Decl             ::=  elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment | PEReference | S | includeSect | ignoreSect
  %%
  %%  InternalDecl is a proper subset of Decl.
  %%  ExternalDecl equals Decl.
  %%
  %%  We unify them for parsing purposes to make handling of plausible
  %%  errors more robust.  (In particular, we anticipate that manual
  %%  movement of decls from the external subset to the internal subset
  %%  could introduce errors, as could mistakes made by document authors
  %%  confused by the similarity of the two subsets.)
  %% -------------------------------------------------------------------------------------------------

  def print_Decl decl : UString =
    case decl of
      | Element     decl         -> print_ElementDecl  decl
      | Attributes  decl         -> print_AttlistDecl  decl
      | Entity      decl         -> print_EntityDecl   decl
      | Notation    decl         -> print_NotationDecl decl
      | PI          decl         -> print_PI           decl
      | Comment     decl         -> print_Comment      decl
      | PEReference peref        -> print_PEReference  peref
      | WhiteSpace  white        -> print_WhiteSpace   white
      | Include     include_sect -> print_IncludeSect  include_sect
      | Ignore      ignore_sect  -> print_IgnoreSect   ignore_sect

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

  def print_ExternalDTD {textdecl, decls} =
    (print_TextDecl textdecl) ^ (print_ExternalDecls decls)

  %% -------------------------------------------------------------------------------------------------
  %%  [K16]  ExternalDecls       ::=  ExternalDecl*
  %% -------------------------------------------------------------------------------------------------

  def print_ExternalDecls decls =
    foldl (fn (result, decl) -> result ^ print_ExternalDecl decl) [] decls

  %% -------------------------------------------------------------------------------------------------
  %%  [K17]  ExternalDecl        ::=  Decl
  %% -------------------------------------------------------------------------------------------------

  def print_ExternalDecl decl =
    print_Decl decl

  %% -------------------------------------------------------------------------------------------------
  %%  [K18]  includeSect         ::=  '<![' S? 'INCLUDE' S? '[' ExternalDecls ']]>'
  %% -------------------------------------------------------------------------------------------------

  def print_IncludeSect {w1, w2, decls} =
    (ustring "<![") ^ w1 ^ (ustring "INCLUDE") ^ w2 ^ (ustring "[") ^ (print_ExternalDecls decls) ^ (ustring "]]>")

  %% -------------------------------------------------------------------------------------------------
  %%  [K19]  ignoreSect          ::=  '<![' S? 'IGNORE' S? '[' ignoreSectContents ']]>'
  %% -------------------------------------------------------------------------------------------------

  def print_IgnoreSect {w1, w2, contents} =
    (ustring "<![") ^ w1 ^ (ustring "IGNORE")  ^ w2 ^ (ustring "[") ^ (print_IgnoreSectContents contents) ^ (ustring "]]>")

  %% -------------------------------------------------------------------------------------------------
  %%   [64]  ignoreSectContents  ::=  Ignore ('<![' ignoreSectContents ']]>' Ignore)*
  %% -------------------------------------------------------------------------------------------------

  def print_IgnoreSectContents {prefix, contents} =
    (print_Ignore prefix) ^
    (foldl (fn (result, (contents :IgnoreSectContents, ignore : Ignore)) ->
	    result ^
	    (ustring "<![") ^ (print_IgnoreSectContents contents) ^ (ustring "]]>") ^
	    (print_Ignore ignore))
           []
	   contents)

  %% -------------------------------------------------------------------------------------------------
  %%   [65]  Ignore              ::=  Char* - (Char* ('<![' | ']]>') Char*)
  %% -------------------------------------------------------------------------------------------------

  def print_Ignore ustr = ustr

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD ElementDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: An element type declaration takes the form:]
  %%
  %%   [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>'
  %%
  %%                                                             [VC: Unique Element Type Declaration]
  %%
  %%  [Definition: An element type has element content when elements of that type must contain only
  %%   child elements (no character data), optionally separated by white space (characters matching
  %%   the nonterminal S).]
  %%
  %%  [Definition: In this case, the constraint includes a content model, a simple grammar governing
  %%   the allowed types of the child elements and the order in which they are allowed to appear.]
  %%
  %%   [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children
  %%
  %%  *[47]  children     ::=  (choice | seq) ('?' | '*' | '+')?
  %%    ==>
  %%  [K20]  children     ::=  cp
  %%                                                             [KWFC: Children Decl]
  %%
  %%  The grammar is built on content particles (cps), which consist of names, choice lists of
  %%  content particles, or sequence lists of content particles:
  %%
  %%  *[48]  cp           ::=  (Name | choice | seq) ('?' | '*' | '+')?
  %%    ==>
  %%  [K21]  cp           ::=  cpbody Repeater
  %%  [K22]  cpbody       ::=  Name | choice | seq
  %%
  %%  *[49]  choice       ::=  '(' S? cp ( S? '|' S? cp )+ S? ')'
  %%    ==>
  %%  [K23]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')'
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%  *[50]  seq          ::=  '(' S? cp ( S? ',' S? cp )* S? ')'
  %%    ==>
  %%  [K24]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')'
  %%                                                             [VC: Proper Group/PE Nesting]
  %%
  %%  [K25]  Repeater     ::=  ('?' | '*' | '+' | '')
  %%
  %%  [Definition: An element type has mixed content when elements of that type may contain
  %%   character data, optionally interspersed with child elements.] In this case, the types of
  %%   the child elements may be constrained, but not their order or their number of occurrences:
  %%
  %%   [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')'
  %%
  %%                                                             [VC: Proper Group/PE Nesting]
  %%                                                             [VC: No Duplicate Types]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [45]  elementdecl  ::=  '<!ELEMENT' S Name S contentspec S? '>'
  %% -------------------------------------------------------------------------------------------------

  def print_ElementDecl {w1, name, w2,contents, w3} : UString =
    w1 ^ name ^ w2 ^ (print_ContentSpec contents) ^ w3

  %% -------------------------------------------------------------------------------------------------
  %%   [46]  contentspec  ::=  'EMPTY' | 'ANY' | Mixed | children
  %% -------------------------------------------------------------------------------------------------

  def print_ContentSpec x =
    case x of
      | Empty              -> (ustring "EMPTY")
      | Any                -> (ustring "ANY")
      | Mixed    mixed     -> print_Mixed mixed
      | Children children  -> print_Children children

  %% -------------------------------------------------------------------------------------------------
  %%  [K20]  children     ::=  cp
  %%                                                             [KWFC: Children Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Children Decl]                         [K20] -- well_formed_children?
  %%
  %%    The basic production for children in the contentspec of an elementdecl in the DTD
  %%    must be a choice or seq, not a simple name.
  %% -------------------------------------------------------------------------------------------------

  def print_Children children =
    print_CP children

  %% -------------------------------------------------------------------------------------------------
  %%  [K21]  cp           ::=  cpbody Repeater
  %% -------------------------------------------------------------------------------------------------

  def print_CP {body, repeater} =
    (print_CPBody body)
    ^
    (print_Repeater repeater)

  %% -------------------------------------------------------------------------------------------------
  %%  [K22]  cpbody       ::=  Name | choice | seq
  %% -------------------------------------------------------------------------------------------------

  def print_CPBody body =
    case body of
      | Name   name   -> print_Name   name
      | Choice choice -> print_Choice choice
      | Seq    seq    -> print_Seq    seq

  %% -------------------------------------------------------------------------------------------------
  %%  [K23]  choice       ::=  '(' S? cp S? ( '|' S? cp S? )+ ')'
  %% -------------------------------------------------------------------------------------------------

  def print_Choice choice =
    let alternatives = choice.alternatives in
    (ustring "(")
    ^
    (foldl (fn (result, (w1, cp, w2)) ->
	    result
	    ^ (case result of [] -> [] | _ -> ustring "|")
	    ^ w1
	    ^ (print_CP cp)
	    ^ w2)
           []
	   alternatives)
    ^
    (ustring ")")

  %% -------------------------------------------------------------------------------------------------
  %%  [K24]  seq          ::=  '(' S? cp S? ( ',' S? cp S? )* ')'
  %% -------------------------------------------------------------------------------------------------

  def print_Seq seq =
    let items = seq.items in
    (ustring "(")
    ^
    (foldl (fn (result, (w1, cp, w2)) ->
	    result
	    ^ (case result of [] -> [] | _ -> ustring ",")
	    ^ w1
	    ^ (print_CP cp)
	    ^ w2)
           []
	   items)
    ^
    (ustring ")")

  %% -------------------------------------------------------------------------------------------------
  %%  [K25]  Repeater     ::=  ('?' | '*' | '+' | '')
  %% -------------------------------------------------------------------------------------------------

  def print_Repeater repeater =
    ustring (case repeater of
	       | ZeroOrOne  -> "?"
	       | ZeroOrMore -> "*"
	       | OneOrMore  -> "+"
	       | One        -> "")

  %% -------------------------------------------------------------------------------------------------
  %%   [51]  Mixed        ::=  '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')'
  %% -------------------------------------------------------------------------------------------------
  %%  Note: if the list is empty, it ends with ")", if non-empty, ")*"
  %% -------------------------------------------------------------------------------------------------

  def print_Mixed {w1, names, w2} =
    (ustring "(")
    ^ w1
    ^ (ustring "#PCDATA")
    ^ (foldl (fn (result, (w3, w4, name)) -> result ^ w3 ^ (ustring "|") ^ w4 ^ name) [] names)
    ^ w2
    ^ (case names of
	 | [] -> (ustring ")")
	 | _  -> (ustring ")*"))

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD AttListDecl                                                                     %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: Attribute-list declarations specify the name, data type, and default value
  %%   (if any) of each attribute associated with a given element type:]
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
  %%
  %%  [Definition: Enumerated attributes can take one of a list of values provided in the
  %%   declaration].
  %%
  %%  *[57]  EnumeratedType  ::=  NotationType | Enumeration
  %%
  %%    ==>
  %%
  %%  [K26]  AttType         ::=  'CDATA'
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
  %%                                                             [VC:  Fixed Attribute Default]
  %%
  %%  In an attribute declaration, #REQUIRED means that the attribute must always be provided,
  %%  #IMPLIED that no default value is provided.
  %%
  %%  [Definition: If the declaration is neither #REQUIRED nor #IMPLIED, then the AttValue value
  %%   contains the declared default value; the #FIXED keyword states that the attribute must
  %%   always have the default value. If a default value is declared, when an XML processor
  %%   encounters an omitted attribute, it is to behave as though the attribute were present with
  %%   the declared default value.]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [52]  AttlistDecl     ::=  '<!ATTLIST' S Name AttDef* S? '>'
  %% -------------------------------------------------------------------------------------------------

  def print_AttlistDecl {w1, name, defs, w2} =
    (ustring "<!ATTLIST") ^ w1 ^ name ^
    (foldl (fn (result, att_def) -> result ^ (print_AttDef att_def)) [] defs) ^
    w2 ^ (ustring ">")

  %% -------------------------------------------------------------------------------------------------
  %%   [53]  AttDef          ::=  S Name S AttType S DefaultDecl
  %% -------------------------------------------------------------------------------------------------

  def print_AttDef {w1, name, w2, att_type, w3, default} =
    w1 ^ name ^ w2 ^ (print_AttType att_type) ^ w3 ^ (print_DefaultDecl default)

  %% -------------------------------------------------------------------------------------------------
  %%  [K26]  AttType         ::=  'CDATA'
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
  %% -------------------------------------------------------------------------------------------------

  def print_AttType x =
    case x of
      | String            -> (ustring "CDATA")
      | ID                -> (ustring "ID")
      | IDRef             -> (ustring "IDREF")
      | IDRefs            -> (ustring "IDREFS")
      | Entity            -> (ustring "ENTITY")
      | Entities          -> (ustring "ENTITIES")
      | NmToken           -> (ustring "NMTOKEN")
      | NmTokens          -> (ustring "NMTOKENS")
      | Notation    ntype -> print_NotationType ntype
      | Enumeration enum  -> print_Enumeration  enum

  %% -------------------------------------------------------------------------------------------------
  %%   [58]  NotationType    ::=  'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')'
  %% -------------------------------------------------------------------------------------------------

  def print_NotationType {w1, w2, first, others, w3} =
    (ustring "NOTATION") ^ w1 ^ (ustring "(") ^ w2 ^ first ^
    (foldl (fn (result, (w4, w5, name)) -> result ^ w4 ^ (ustring "|") ^ w5 ^ name) [] others) ^
    w3 ^ (ustring ")")

  %% -------------------------------------------------------------------------------------------------
  %%   [59]  Enumeration     ::=  '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')'
  %% -------------------------------------------------------------------------------------------------

  def print_Enumeration {w1, first, others, w2} =
    (ustring "(") ^ w1 ^ (print_NmToken first) ^
    (foldl (fn (result, (w3, w4, name)) -> result ^ w3 ^ (ustring "|") ^ w4 ^ name) [] others) ^
    w2 ^ (ustring ")")

  %% -------------------------------------------------------------------------------------------------
  %%   [60]  DefaultDecl     ::=  '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue)
  %% -------------------------------------------------------------------------------------------------

  def print_DefaultDecl x =
    case x of
      | Required -> (ustring "#REQUIRED")
      | Implied  -> (ustring "#IMPLIED")
      | Fixed    (opt_w1, att_value) ->
        (case opt_w1 of
	   | Some w1 -> (ustring "#FIXED") ^ w1
	   | _ -> [])
	^
	(print_AttValue att_value)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          DTD EntityDecl                                                                      %%%
  %%%          DTD NotationDecl                                                                    %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [Definition: Entities are declared thus:]
  %%
  %%   [70]  EntityDecl     ::=  GEDecl | PEDecl
  %%
  %%   [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %%
  %%   [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %%
  %%   [73]  EntityDef      ::=  EntityValue | (ExternalID NDataDecl?)
  %%
  %%   [Definition: The literal entity value is the quoted string actually present in the entity
  %%    declaration, corresponding to the non-terminal EntityValue.]
  %%
  %%   [Definition: The replacement text is the content of the entity, after replacement of
  %%    character references and parameter-entity references.]
  %%
  %%   [Definition: If the entity definition is an EntityValue, the defined entity is called an
  %%    internal entity. There is no separate physical storage object, and the content of the
  %%    entity is given in the declaration.]
  %%
  %%   If the NDataDecl is present, this is a general unparsed entity; otherwise it is a parsed entity.
  %%
  %%   4.3.2 Well-Formed Parsed Entities:
  %%
  %%  "An external general parsed entity is well-formed if it matches the production labeled
  %%   'extParsedEnt'."
  %%
  %%  "An internal general parsed entity is well-formed if its replacement text matches the
  %%   production labeled content."
  %%
  %%  "A consequence of well-formedness in [general] entities is that the logical and physical
  %%   structures in an XML document are properly nested; no start-tag, end-tag, empty-element
  %%   tag, element, comment, processing instruction, character reference, or entity reference
  %%   can begin in one [general] entity and end in another."  Kestrel note: [general] added,
  %%   since sentence would be false for parameter entities, as one can have a start tag in
  %%   in one parameter entity and the matching end tag in antoher.
  %%
  %%   [74]  PEDef          ::=  EntityValue | ExternalID
  %%                                                             [VC:  Proper Declaration/PE Nesting]
  %%
  %%   [76]  NDataDecl      ::=  S 'NDATA' S Name
  %%                                                             [VC: Notation Declared]
  %%
  %% ------------------------------------------------------------------------------------------------
  %%
  %%  [Definition: If the entity is not internal, it is an external entity, declared as follows:]
  %%
  %%  *[75]  ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral
  %%  *[83]  PublicID       ::=  'PUBLIC' S PubidLiteral
  %%    ==>
  %%  [K27]  ExternalID     ::=  GenericID
  %%                                                             [KWFC: External ID]
  %%
  %%  [K28]  GenericID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral (S SystemLiteral)?
  %%
  %%  GenericID = ExternalID + PublicID,   but only GenericID and ExternalID are actually used,
  %%                                       so PublicID can be dropped
  %%
  %%  [Definition: The SystemLiteral is called the entity's system identifier. It is a URI reference
  %%  (as defined in [IETF RFC 2396], updated by [IETF RFC 2732]), meant to be dereferenced to obtain
  %%   input for the XML processor to construct the entity's replacement text.]
  %%
  %%  It is an error for a fragment identifier (beginning with a # character) to be part of a system
  %%  identifier. Unless otherwise provided by information outside the scope of this specification
  %%  (e.g. a special XML element type defined by a particular DTD, or a processing instruction
  %%  defined by a particular application specification), relative URIs are relative to the location
  %%  of the resource within which the entity declaration occurs. A URI might thus be relative to
  %%  the document entity, to the entity containing the external DTD subset, or to some other
  %%  external parameter entity.
  %%
  %%  URI references require encoding and escaping of certain characters. The disallowed characters
  %%  include all non-ASCII characters, plus the excluded characters listed in Section 2.4 of
  %%  [IETF RFC 2396], except for the number sign (#) and percent sign (%) characters and the square
  %%  bracket characters re-allowed in [IETF RFC 2732]. Disallowed characters must be escaped as follows:
  %%
  %%    1.  Each disallowed character is converted to UTF-8 [IETF RFC 2279] as one or more bytes.
  %%
  %%    2.  Any octets corresponding to a disallowed character are escaped with the URI escaping
  %%        mechanism (that is, converted to %HH, where HH is the hexadecimal notation of the byte value).
  %%
  %%    3.  The original character is replaced by the resulting character sequence.
  %%
  %% -------------------------------------------------------------------------------------------------
  %%
  %%  [Definition: Notations identify by name the format of unparsed entities, the format of
  %%   elements which bear a notation attribute, or the application to which a processing
  %%   instruction is addressed.]
  %%
  %%  [Definition: Notation declarations provide a name for the notation, for use in entity and
  %%   attribute-list declarations and in attribute specifications, and an external identifier
  %%   for the notation which may allow an XML processor or its client application to locate a
  %%   helper application capable of processing data in the given notation.]
  %%
  %%  [Definition: In addition to a system identifier, an external identifier may include a public
  %%   identifier.]
  %%
  %%  *[82]  NotationDecl   ::=  '<!NOTATION' S Name S (ExternalID | PublicID) S? '>'
  %%    ==>
  %%  [K29]  NotationDecl   ::=  '<!NOTATION' S Name S GenericID S? '>'
  %%
  %%                                                             [VC: Unique Notation Name]
  %%
  %%  An XML processor attempting to retrieve the entity's content may use the public identifier
  %%  to try to generate an alternative URI reference. If the processor is unable to do so, it
  %%  must use the URI reference specified in the system literal. Before a match is attempted,
  %%  all strings of white space in the public identifier must be normalized to single space
  %%  characters (#x20), and leading and trailing white space must be removed.
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [70]  EntityDecl     ::=  GEDecl | PEDecl
  %% -------------------------------------------------------------------------------------------------

  def print_EntityDecl x =
   case x of
    | GE decl -> print_GEDecl decl
    | PE decl -> print_PEDecl decl

  %% -------------------------------------------------------------------------------------------------
  %%   [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %% -------------------------------------------------------------------------------------------------

  def print_GEDecl {w1, name, w2, edef, w3} =
    (ustring "<!ENTITY") ^ w1 ^ name ^ w2 ^ (print_EntityDef edef) ^ w3 ^ (ustring ">")

  %% -------------------------------------------------------------------------------------------------
  %%   [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %% -------------------------------------------------------------------------------------------------

  def print_PEDecl {w1, w2, name, w3, pedef, w4} =
    (ustring "<!ENTITY") ^ w1 ^ (ustring "%") ^ w2 ^ name ^ w3 ^ (print_PEDef pedef) ^ w4 ^ (ustring ">")

  %% -------------------------------------------------------------------------------------------------
  %%   [73]  EntityDef      ::=  EntityValue | (ExternalID NDataDecl?)
  %%
  %%  4.3.2 Well-Formed Parsed Entities:
  %%
  %%  "An external general parsed entity is well-formed if it matches the production labeled
  %%   'extParsedEnt'."
  %%
  %%  "An internal general parsed entity is well-formed if its replacement text matches the
  %%   production labeled content."
  %%
  %%  "A consequence of well-formedness in [general] entities is that the logical and physical
  %%   structures in an XML document are properly nested; no start-tag, end-tag, empty-element
  %%   tag, element, comment, processing instruction, character reference, or entity reference
  %%   can begin in one [general] entity and end in another."  Kestrel note: [general] added,
  %%   since sentence would be false for parameter entities, as one can have a start tag in
  %%   in one parameter entity and the matching end tag in antoher.
  %%
  %% -------------------------------------------------------------------------------------------------

  def print_EntityDef x =
   case x of
     | Value    value  -> print_EntityValue value
     | External (id, opt_decl) ->
       (print_ExternalID id) ^
       (case opt_decl of
	  | Some ndata_decl -> print_NDataDecl ndata_decl
	  | _ -> [])

  %% -------------------------------------------------------------------------------------------------
  %%   [74]  PEDef          ::=  EntityValue | ExternalID
  %%
  %%  4.3.2 Well-Formed Parsed Entities:
  %%
  %%  "All external parameter entities are well-formed by definition."
  %%  "All internal parameter entities are well-formed by definition."
  %%
  %%  but note validity constraint:
  %%
  %%  [VC: Proper Declaration/PE Nesting]           [74] [K11] *[29]
  %%
  %%    Parameter-entity replacement text must be properly nested with markup declarations.
  %%
  %%    That is to say, if either the first character or the last character of a markup declaration
  %%    (markupdecl above) is contained in the replacement text for a parameter-entity reference,
  %%    both must be contained in the same replacement text.
  %%
  %% -------------------------------------------------------------------------------------------------

  def print_PEDef x =
    case x of
     | Value    value -> print_EntityValue value
     | External id    -> print_ExternalID id

  %% -------------------------------------------------------------------------------------------------
  %%   [76]  NDataDecl      ::=  S 'NDATA' S Name
  %% -------------------------------------------------------------------------------------------------

  def print_NDataDecl {w1, w2, name} =
    w1 ^ (ustring "NDATA") ^ w2 ^ name

  %% -------------------------------------------------------------------------------------------------
  %%  [K27]  ExternalID     ::=  GenericID
  %%                                                             [KWFC: External ID]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: External ID]                           [K27] *[75] -- well_formed_external_id?
  %%
  %%    ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral
  %% -------------------------------------------------------------------------------------------------

  def print_ExternalID id = print_GenericID id

  %% -------------------------------------------------------------------------------------------------
  %%  [K28]  GenericID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral (S SystemLiteral)?
  %% -------------------------------------------------------------------------------------------------

  def print_GenericID id =
   case id.public of
     | Some pub_lit ->
       (ustring "PUBLIC") ^ id.w1 ^ (print_PubidLiteral pub_lit) ^
       (case id.system of
	  | Some sys_lit -> (id.w2 ^ (print_SystemLiteral sys_lit))
	  | None         -> [])
     | _ ->
       (ustring "SYSTEM") ^
       (case id.system of
	  | Some sys_lit -> (id.w2 ^ (print_SystemLiteral sys_lit))
	  | None         -> [])

  %% -------------------------------------------------------------------------------------------------
  %%  [K29]  NotationDecl   ::=  '<!NOTATION' S Name S GenericID S? '>'
  %% -------------------------------------------------------------------------------------------------

  def print_NotationDecl {w1, name, w2, id, w3} =
    (ustring "<!NOTATION") ^ w1 ^ name ^ w2 ^ (print_GenericID id) ^ w3 ^ (ustring ">")

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          PI                                                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: Processing instructions (PIs) allow documents to contain instructions for
  %%   applications.]
  %%
  %%  *[16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'
  %%    ==>
  %%  [K30]  PI        ::= '<?' PITarget (S PIValue)? '?>'
  %%  [K31]  PIValue   ::= Char* - (Char* '?>' Char*)
  %%
  %%   [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K30]  PI        ::= '<?' PITarget (S PIValue)? '?>'
  %%   [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%  [K31]  PIValue   ::= Char* - (Char* '?>' Char*)
  %% -------------------------------------------------------------------------------------------------

  def print_PI {target, value} =
    (ustring "<?")
    ^ target
    ^ (case value of
	 | Some (whitespace, text) -> whitespace ^ text
	 | _ -> [])
    ^ (ustring "?>")

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Element                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: Each XML document contains one or more elements, the boundaries of which are either
  %%   delimited by start-tags and end-tags, or, for empty elements, by an empty-element tag.
  %%   Each element has a type, identified by name, sometimes called its "generic identifier" (GI),
  %%   and may have a set of attribute specifications.]
  %%
  %%   [39]  element  ::=  EmptyElemTag | STag content ETag
  %%                                                             [WFC: Element Type Match]
  %%                                                             [VC:  Element Valid]
  %%                                                             [KVC: Element Valid]
  %%
  %%  [Definition: The beginning of every non-empty XML element is marked by a start-tag.]
  %%
  %%  The Name in the start- and end-tags gives the element's type.
  %%
  %%  *[40]  STag          ::=  '<' Name (S Attribute)* S? '>'
  %%                                                            *[WFC: Unique Att Spec]
  %%    ==>
  %%  [K32]  STag          ::=  ElementTag
  %%                                                             [KWFC: Start Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%
  %%  [Definition: The Name-AttValue pairs are referred to as the attribute specifications of the
  %%   element],
  %%
  %%  [Definition: with the Name in each pair referred to as the attribute name] and
  %%
  %%  [Definition: the content of the AttValue (the text between the ' or " delimiters) as the
  %%   attribute value.]
  %%
  %%  Note that the order of attribute specifications in a start-tag or empty-element tag is not significant.
  %%
  %%  [Definition: The end of every element that begins with a start-tag must be marked by an
  %%   end-tag containing a name that echoes the element's type as given in the start-tag:]
  %%
  %%  *[42]  ETag          ::=  '</' Name S? '>'
  %%    ==>
  %%  [K33]  ETag          ::=  ElementTag
  %%                                                             [KWFC: End Tag]
  %%
  %%  [Definition: The text between the start-tag and end-tag is called the element's content:]
  %%
  %%  Note: Given the way Kestrel uses the chardata in *[43] for indentation, it makes more sense to
  %%        group it as in [K34].  (See print_Element in XML_Printer.sw)
  %%
  %%  *[43]  content       ::=  CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
  %%    ==>
  %%  [K34]  content       ::=  (CharData? content_item)* CharData?
  %%  [K35]  content_item  ::=  element | Reference | CDSect | PI | Comment
  %%
  %%  [Definition: An element with no content is said to be empty.]
  %%
  %%  The representation of an empty element is either a start-tag immediately followed by an
  %%  end-tag, or an empty-element tag.
  %%
  %%  [Definition: An empty-element tag takes a special form:]
  %%
  %%  *[44]  EmptyElemTag  ::=  '<' Name (S Attribute)* S? '/>' 60]
  %%                                                             [WFC: Unique Att Spec]
  %%    ==>
  %%  [K36]  EmptyElemTag  ::=  ElementTag
  %%                                                             [KWFC: Empty Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%   [39]  element  ::=  EmptyElemTag | STag content ETag
  %%                                                             [WFC: Element Type Match]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Element Type Match]                     [39]  -- element_types_match?
  %%
  %%    The Name in an element's end-tag must match the element type in the start-tag.
  %% -------------------------------------------------------------------------------------------------

  def print_Element element =
    case element of

      | Empty tag ->
        print_EmptyElemTag tag

      | Full  elt -> 
	print_FullElement elt

  def print_FullElement {stag, content, etag} =
    (print_STag    stag)    ^
    (print_Content content) ^
    (print_ETag    etag)

  %% -------------------------------------------------------------------------------------------------
  %%  [K32]  STag          ::=  ElementTag
  %%                                                             [KWFC: Start Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Start Tag]                             [K32] *[40] -- well_formed_start_tag?
  %%
  %%    STag  ::=  '<'  Name  (S Attribute)*  S?  '>'
  %%    where Name is not a variant of 'xml'
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Unique Att Spec]                        [K32] [K36] *[40] *[44] -- unique_attributes?
  %%
  %%    No attribute name may appear more than once in the same start-tag or empty-element tag.
  %% -------------------------------------------------------------------------------------------------

  def print_STag         tag = print_ElementTag tag

  %% ----------------------------------------------------------------------------------------------------
  %%  [K33]  ETag          ::=  ElementTag
  %%                                                             [KWFC: End Tag]
  %% ----------------------------------------------------------------------------------------------------
  %%  [KWFC: End Tag]                               [K33] *[42] -- well_formed_end_tag?
  %%
  %%    ETag  ::=  '</'  Name  S?  '>'
  %%    where Name is not a variant of 'xml'
  %% ----------------------------------------------------------------------------------------------------

  def print_ETag         tag = print_ElementTag tag

  %% -------------------------------------------------------------------------------------------------
  %%  [K34]  content       ::=  (CharData? content_item)* CharData?
  %% -------------------------------------------------------------------------------------------------

  def print_Content {items, trailer} =
    (foldl (fn (result, (opt_char_data, item)) ->
	    result ^
	    (case opt_char_data of
	       | Some char_data -> print_CharData char_data
	       | _ -> [])
	    ^
	    (print_Content_Item item))
           []
	   items)
    ^
    (case trailer of
       | Some char_data -> print_CharData char_data
       | _ -> [])

  %% -------------------------------------------------------------------------------------------------
  %%  [K35]  content_item  ::=  element | Reference | CDSect | PI | Comment
  %% -------------------------------------------------------------------------------------------------

  def print_Content_Item item =
    case item of
      | Element   element -> print_Element   element
      | Reference ref     -> print_Reference ref
      | CDSect    cd_sect -> print_CDSect    cd_sect
      | PI        pi      -> print_PI        pi
      | Comment   comment -> print_Comment   comment

  %% -------------------------------------------------------------------------------------------------
  %%  [K36]  EmptyElemTag  ::=  ElementTag
  %%                                                             [KWFC: Empty Tag]
  %%                                                             [WFC:  Unique Att Spec]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Empty Tag]                             [K36] *[44] -- well_formed_empty_tag?
  %%
  %%    EmptyElemTag  ::=  '<'  Name  (S Attribute)*  S?  '/>'
  %%    where Name is not a variant of 'xml'
  %%
  %%  [WFC: Unique Att Spec]                        [K32] [K36] *[40] *[44] -- unique_attributes?
  %%
  %%    No attribute name may appear more than once in the same start-tag or empty-element tag.
  %% -------------------------------------------------------------------------------------------------

  def print_EmptyElemTag tag = print_ElementTag tag

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
  %%  "An internal general parsed entity is well-formed if its replacement text matches the
  %%   production labeled content."
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def print_extParsedEnt {text, content} =
    (print_TextDecl text) ^ (print_Content content)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Character_Strings                                                                   %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%   [3]  S         ::=  (#x20 | #x9 | #xD | #xA)+
  %%
  %%  [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %%
  %%  [Definition: Comments may appear anywhere in a document outside other markup; in addition,
  %%   they may appear within the document type declaration at places allowed by the grammar.
  %%   They are not part of the document's character data; an XML processor may, but need not,
  %%   make it possible for an application to retrieve the text of comments. For compatibility,
  %%   the string "--" (double-hyphen) must not occur within comments.]
  %%
  %%  Parameter entity references are not recognized within comments.
  %%
  %%  [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %%
  %%
  %%  [Definition: CDATA sections may occur anywhere character data may occur; they are used to
  %%   escape blocks of text containing characters which would otherwise be recognized as markup.
  %%   CDATA sections begin with the string "<![CDATA[" and end with the string "]]>":]
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

  %% -------------------------------------------------------------------------------------------------
  %%   [3]  S         ::=  (#x20 | #x9 | #xD | #xA)+
  %% -------------------------------------------------------------------------------------------------

  def print_WhiteSpace x = x

  %% -------------------------------------------------------------------------------------------------
  %%  [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %% -------------------------------------------------------------------------------------------------

  def print_CharData x = x

  %% -------------------------------------------------------------------------------------------------
  %%  [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %% -------------------------------------------------------------------------------------------------

  def print_Comment x =
    (ustring "<!--") ^ x ^ (ustring "-->")

  %% -------------------------------------------------------------------------------------------------
  %%  [18]  CDSect    ::=  CDStart CData CDEnd
  %%  [19]  CDStart   ::=  '<![CDATA['
  %%  [20]  CData     ::=  (Char* - (Char* ']]>' Char*))
  %%  [21]  CDEnd     ::=  ']]>'
  %% -------------------------------------------------------------------------------------------------

  def print_CDSect cdsect =
   (ustring "<![CDATA[")  ^ cdsect.cdata ^ (ustring "]]>")

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Literals                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%    [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %%
  %%   [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %%                                                             [WFC: No < in Attribute Values]
  %%
  %%  *[11]  SystemLiteral   ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %%    ==>
  %%  [K37]  SystemuLiteral  ::=  QuotedText
  %%
  %%  *[12]  PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'"
  %%    ==>
  %%  [K38]  PubidLiteral    ::=  QuotedText
  %%                                                             [KWFC: Pubid Literal]
  %%
  %%   [13]  PubidChar       ::=  #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
  %%
  %%  [K39]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%    [9]  EntityValue     ::=  '"' ([^%&"] | PEReference | Reference)* '"'  |  "'" ([^%&'] | PEReference | Reference)* "'"
  %% -------------------------------------------------------------------------------------------------

  def print_EntityValue {qchar, items} =
    [qchar] ^ (foldl (fn (result, item) -> result ^ (print_EntityValue_Item item)) [] items) ^ [qchar]

  def print_EntityValue_Item x =
   case x of
     | NonRef ustr   -> ustr
     | PERef  pe_ref -> print_PEReference pe_ref
     | Ref    ref    -> print_Reference ref

  %% -------------------------------------------------------------------------------------------------
  %%   [10]  AttValue        ::=  '"' ([^<&"] | Reference)* '"' |  "'" ([^<&'] | Reference)* "'"
  %%
  %%                                                             [WFC: No < in Attribute Values]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: No < in Attribute Values]               [10] [60] [K9] *[41]
  %%
  %%    The replacement text of any entity referred to directly or indirectly in an attribute value
  %%     must not contain a <.
  %%
  %%  TODO
  %% -------------------------------------------------------------------------------------------------

  %% For now at least, print the component items, as opposed to their composite value.
  def print_AttValue {qchar, items, value=_} =
    [qchar] ^ (foldl (fn (result, item) -> result ^ (print_AttValue_Item item)) [] items) ^ [qchar]

  def print_AttValue_Item x =
    case x of
      | NonRef ustr -> ustr
      | Ref    ref  -> print_Reference ref

  %% -------------------------------------------------------------------------------------------------
  %%  [K37]  SystemLiteral   ::=  QuotedText
  %% -------------------------------------------------------------------------------------------------

  def print_SystemLiteral x = print_QuotedText x

  %% -------------------------------------------------------------------------------------------------
  %%  [K38]  PubidLiteral    ::=  QuotedText
  %%                                                             [KWFC: Pubid Literal]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Pubid Literal]                         [K38] *[12] -- well_formed_pubid_literal?
  %%
  %%    All chars in a pubid literal are PubidChar's :
  %%    PubidLiteral    ::=  '"' PubidChar* '"' | "'" (PubidChar - "'")* "'"
  %% -------------------------------------------------------------------------------------------------

  def print_PubidLiteral  x = print_QuotedText x

  %% -------------------------------------------------------------------------------------------------
  %%  [K39]  QuotedText      ::=  ('"' [^"]* '"') | ("'" [^']* "'")
  %% -------------------------------------------------------------------------------------------------

  def print_QuotedText qtext = print_BoundedText qtext

  def print_BoundedText {qchar, text} =
    qchar :: (text ^ (qchar :: []))

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          References                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: A character reference refers to a specific character in the ISO/IEC 10646
  %%   character set, for example one not directly accessible from available input devices.]
  %%
  %%  [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';'
  %%
  %%                                                             [WFC: Legal Character]
  %%
  %%  [67]  Reference    ::=  EntityRef | CharRef
  %%
  %%  [Definition: An entity reference refers to the content of a named entity.]
  %%
  %%  [Definition: References to parsed general entities use ampersand (&) and semicolon (;) as
  %%   delimiters.]
  %%
  %%  [Definition: Parameter-entity references use percent-sign (%) and semicolon (;) as delimiters.]
  %%
  %%  [68]  EntityRef    ::=  '&' Name ';'
  %%                                                             [WFC: Entity Declared]
  %%                                                             [WFC: Parsed Entity]
  %%                                                             [WFC: No Recursion]
  %%                                                             [VC:  Entity Declared]
  %%
  %%  [Definition: Entity and character references can both be used to escape the left angle bracket,
  %%   ampersand, and other delimiters. A set of general entities (amp, lt, gt, apos, quot) is
  %%   specified for this purpose. Numeric character references may also be used; they are expanded
  %%   immediately when recognized and must be treated as character data, so the numeric character
  %%   references "&#60;" and "&#38;" may be used to escape < and & when they occur in character
  %%   data.]
  %%
  %%  [69]  PEReference  ::=  '%' Name ';'
  %%                                                             [WFC: In DTD]
  %%                                                             [WFC: No Recursion]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [VC:  Proper Group/PE Nesting] (implicit)
  %%
  %%  [Definition: An entity is included when its replacement text is retrieved and processed,
  %%   in place of the reference itself, as though it were part of the document at the location
  %%   the reference was recognized.]
  %%
  %%  The replacement text may contain both character data and (except for parameter entities)
  %%  markup, which must be recognized in the usual way.  (The string "AT&amp;T;" expands to "AT&T;"
  %%  and the remaining ampersand is not recognized as an entity-reference delimiter.)
  %%  A character reference is included when the indicated character is processed in place of the
  %%  reference itself.
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';'
  %%
  %%                                                             [WFC: Legal Character]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Legal Character]                        [66] -- char?
  %%
  %%    Characters referred to using character references must match the production for Char.
  %% -------------------------------------------------------------------------------------------------

  def print_CharRef  {style, char} =
    case style of
      | Decimal -> (ustring "&#")  ^ (ustring (Nat.show char)) ^ (ustring ";")
      | Hex     -> (ustring "&#x") ^ (ustring (toHex    char)) ^ (ustring ";")

  %% -------------------------------------------------------------------------------------------------
  %%  [67]  Reference    ::=  EntityRef | CharRef
  %% -------------------------------------------------------------------------------------------------

  def print_Reference x =
    case x of
      | Entity eref -> print_EntityRef eref
      | Char   cref -> print_CharRef   cref

  %% -------------------------------------------------------------------------------------------------
  %%  [68]  EntityRef    ::=  '&' Name ';'
  %%                                                             [WFC: Entity Declared]
  %%                                                             [WFC: Parsed Entity]
  %%                                                             [WFC: No Recursion]
  %%                                                             [VC:  Entity Declared]
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Entity Declared]                        [68]           -- entity_declared?
  %%
  %%    In a document without any DTD, a document with only an internal DTD subset which contains no
  %%    parameter entity references, or a document with "standalone='yes'", for an entity reference
  %%    that does not occur within the external subset or a parameter entity, the Name given in the
  %%    entity reference must match that in an entity declaration that does not occur within the
  %%    external subset or a parameter entity, except that well-formed documents need not declare any
  %%    of the following entities: amp, lt, gt, apos, quot. The declaration of a general entity must
  %%    precede any reference to it which appears in a default value in an attribute-list declaration.
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: Parsed Entity]                          [68]
  %%
  %%    An entity reference must not contain the name of an unparsed entity. Unparsed entities may
  %%    be referred to only in attribute values declared to be of type ENTITY or ENTITIES.
  %%
  %%  TODO
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: No Recursion]                           [68]  [69]
  %%
  %%    A parsed entity must not contain a recursive reference to itself, either directly or
  %%    indirectly.
  %% -------------------------------------------------------------------------------------------------

  def print_EntityRef ref =
    (ustring "&") ^ ref.name ^ (ustring ";")

  %% -------------------------------------------------------------------------------------------------
  %%  [69]  PEReference  ::=  '%' Name ';'
  %%                                                             [WFC: In DTD]
  %%                                                             [WFC: No Recursion]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [VC:  Proper Group/PE Nesting] (implicit)
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: In DTD]                                 [69] (really [31] [K12]) -- no_pe_reference?
  %%
  %%    Parameter-entity references may only appear in the DTD.
  %%    Comment: This includes both the internal and external subsets!
  %%    Comment: This appears to be vacuously true, given the grammar.
  %% -------------------------------------------------------------------------------------------------
  %%  [WFC: No Recursion]                           [68]  [69]
  %%
  %%    A parsed entity must not contain a recursive reference to itself, either directly or
  %%    indirectly.
  %%
  %%  TODO
  %% -------------------------------------------------------------------------------------------------

  def print_PEReference ref =
    (ustring "%") ^ ref.name ^ (ustring ";")

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Names                                                                               %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: A Name is a token beginning with a letter or one of a few punctuation characters,
  %%   and continuing with letters, digits, hyphens, underscores, colons, or full stops, together
  %%   known as name characters.] Names beginning with the string "xml", or any string which would
  %%   match (('X'|'x') ('M'|'m') ('L'|'l')), are reserved for standardization in this or future
  %%   versions of this specification.
  %%
  %%  Note: The Namespaces in XML Recommendation [XML Names] assigns a meaning to names containing
  %%        colon characters. Therefore, authors should not use the colon in XML names except for
  %%        namespace purposes, but XML processors must accept the colon as a name character.
  %%
  %%  An Nmtoken (name token) is any mixture of name characters.
  %%
  %%  [4]  NameChar  ::=  Letter | Digit | '.' | '-' | '_' | ':' | CombiningChar | Extender
  %%  [5]  Name      ::=  (Letter | '_' | ':') (NameChar)*
  %%  [6]  Names     ::=  Name (S Name)*
  %%  [7]  Nmtoken   ::=  (NameChar)+
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [4]  NameChar  ::=  Letter | Digit | '.' | '-' | '_' | ':' | CombiningChar | Extender
  %%  [5]  Name      ::=  (Letter | '_' | ':') (NameChar)*
  %% -------------------------------------------------------------------------------------------------

  def print_Name (name : Name) : UString = name

  %% -------------------------------------------------------------------------------------------------
  %%  [6]  Names     ::=  Name (S Name)*
  %% -------------------------------------------------------------------------------------------------

  def print_Names (first, others) =
    first ^ (foldl (fn (result, (white, name)) -> result ^ white ^ name)
	           []
		   others)

  %% -------------------------------------------------------------------------------------------------
  %%  [7]  Nmtoken   ::=  (NameChar)+
  %% -------------------------------------------------------------------------------------------------

  def print_NmToken (token : NmToken) : UString = token

  %% -------------------------------------------------------------------------------------------------
  %%  [8]  Nmtokens  ::=  Nmtoken (S Nmtoken)*
  %% -------------------------------------------------------------------------------------------------

  def print_NmTokens (first, others) =
    first ^ (foldl (fn (result, (white, token)) -> result ^ white ^ token)
		       []
		       others)

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Chars                                                                               %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: A character is an atomic unit of text as specified by ISO/IEC 10646  [ISO/IEC 10646]
  %%   (see also [ISO/IEC 10646-2000]). Legal characters are tab, carriage return, line feed,
  %%   and the legal characters of Unicode and ISO/IEC 10646. The versions of these standards
  %%   cited in A.1 Normative References were current at the time this document was prepared.
  %%   New characters may be added to these standards by amendments or new editions. Consequently,
  %%   XML processors must accept any character in the range specified for Char. The use of
  %%   "compatibility characters", as defined in section 6.8 of [Unicode] (see also D21 in section
  %%   3.6 of [Unicode3]), is discouraged.]
  %%
  %%
  %%   [2]  Char          ::=  #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
  %%                           /* any Unicode character, excluding the surrogate blocks, FFFE, and FFFF. */
  %%
  %%   [Definitions copied from http://www.unicode.org/book/ch03.pdf :
  %%
  %%      C1:  A process shall interpret Unicode code values as 16-bit quantities.
  %%
  %%      BUT:
  %%
  %%      D25: High-Surrogate : a Unicode code value in the range U+D800 through U+DBFF
  %%
  %%      D26: Low-Surrogate  : a Unicode code value in the range U+DC00 through U+DFFF
  %%
  %%      D27: Surrogate pair: a coded character representation for a single abstract character that
  %%      consists of a sequence of two Unicode values, where the first vlaue of the pair is a
  %%      high-surrogate and the second is a low-surrogate.
  %%
  %%      D28: Unicode scalar value: a number N from 0 to #x10FFFF defined by applying the following
  %%      algorithm to a character sequence S:
  %%         N = U                        If S is a single nonsurrogate value <U>
  %%         N = (H -#xD800) * #x400 +    If S is a surrogate page <H,L>
  %%             (L -#xDC00) + #x10000
  %%
  %%      The reverse mapping from the Unicode scalar value to a surrogate pair is given by
  %%
  %%         H = (S - #x10000) / #x4000 + #xD800
  %%         L = (S - #x10000) % #x4000 + #xDC00
  %%
  %%      A Unicode scalar value is also referred to as a 'code position' or a 'code point' in the
  %%      information industry.
  %%
  %%      D29:  A Unicode (or UCS) transformation format (UTF) transforms each Unicode scalar value
  %%      into a unique seuqence of code values.  ...
  %%
  %%      Any sequence of code values that would correspond to a scalar value greater than #x10FFFF
  %%      is illegal.
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
