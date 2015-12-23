(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

XML qualifying spec

  import Parse_Character_Strings % parse_WhiteSpace

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

  def parse_EntityDecl (start : UChars, allow_pe_refs? : Bool) : Required EntityDecl =
    %% We begin here just past the '<!ENTITY' in rules [71] and [72], looking for
    %% one of the following:
    %%  S       Name S EntityDef S? '>'
    %%  S '%' S Name S PEDef     S? '>'
    {
     (w1, tail) <- parse_WhiteSpace start;
     case tail of

       | 37 :: tail ->
         %% '%'
         {
	  (pe_decl, tail) <- parse_PEDecl (tail, w1, allow_pe_refs?);
	  return (PE pe_decl, tail)
	  }

       | _ ->
         {
	  (ge_decl, tail) <- parse_GEDecl (tail, w1, allow_pe_refs?);
	   return (GE ge_decl, tail)
	  }}

  %% -------------------------------------------------------------------------------------------------
  %%   [71]  GEDecl         ::=  '<!ENTITY' S       Name S EntityDef S? '>'
  %% -------------------------------------------------------------------------------------------------

  def parse_GEDecl (start : UChars,  w1 : WhiteSpace, allow_pe_refs? : Bool) : Required GEDecl =
    %% We begin here just past the first S in rule [71], looing for:
    %%   Name S EntityDef S? '>'
   {
    (name, tail) <- parse_Name       start;
    (w2,   tail) <- parse_WhiteSpace tail;
    (edef, tail) <- parse_EntityDef  tail;
    (w3,   tail) <- parse_WhiteSpace tail;
    case tail of

      | 62 :: tail ->
        %% '>'
        return ({w1   = w1,
		 name = name,
		 w2   = w2,
		 edef = edef,
		 w3   = w3},
		tail)

      | char :: _ ->
	{
	 error {kind        = Syntax,
		requirement = "GEDecl in DTD must terminate with '>'.",
		start       = start,
		tail        = tail,
		peek        = 10,
		we_expected = [("'>'", "to terminate PEDecl")],
		but         = (describe_char char) ^ " was seen instead",
		so_we       = "pretend interpolated '>' was seen"};
	 return ({w1    = w1,
		  name  = name,
		  w2    = w2,
		  edef  = edef,
		  w3    = w3},
		 tail)
	}

      | _ ->
	hard_error {kind        = Syntax,
		    requirement = "GEDecl in DTD must terminate with '>'.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("'>'", "to terminate PEDecl")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}
       }

  %% -------------------------------------------------------------------------------------------------
  %%   [72]  PEDecl         ::=  '<!ENTITY' S '%' S Name S PEDef     S? '>'
  %% -------------------------------------------------------------------------------------------------

  def parse_PEDecl (start : UChars, w1 : WhiteSpace, allow_pe_refs? : Bool) : Required PEDecl =
   %% We begin here just past the % in rule [72], looking for:
   %%   S Name S PEDef S? '>'
   {
    (w2,    tail) <- parse_WhiteSpace start;
    (name,  tail) <- parse_Name       tail;
    (w3,    tail) <- parse_WhiteSpace tail;
    (pedef, tail) <- parse_PEDef      tail;
    (w4,    tail) <- parse_WhiteSpace tail;
    case tail of

      | 62 :: tail ->
        %% '>'
        return ({w1    = w1,
		 w2    = w2,
		 name  = name,
		 w3    = w3,
		 pedef = pedef,
		 w4    = w4},
		tail)

      | char :: _ ->
	{
	 error {kind        = Syntax,
		requirement = "PEDecl in DTD must terminate with '>'.",
		start       = start,
		tail        = tail,
		peek        = 10,
		we_expected = [("'>'", "to terminate PEDecl")],
		but         = (describe_char char) ^ " was seen instead",
		so_we       = "pretend interpolated '>' was seen"};
	 return ({w1    = w1,
		  w2    = w2,
		  name  = name,
		  w3    = w3,
		  pedef = pedef,
		  w4    = w4},
		 tail)
	}

      | _ ->
	hard_error {kind        = Syntax,
		    requirement = "PEDecl in DTD must terminate with '>'.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("'>'", "to terminate PEDecl")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}
       }

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

  def parse_EntityDef (start : UChars) : Required EntityDef =
    case start of

      | 34 :: tail ->
        %% double-quote
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }

      | 39 :: tail ->
        %% apostrophe
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }

      | _ ->
	{
	 (ext_id, tail) <- parse_ExternalID start;
	 (ndata,  tail) <- parse_NDataDecl tail;
	 return (External (ext_id, ndata),
		tail)
	}

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

  def parse_PEDef (start : UChars) : Required PEDef =
    case start of

      | 34 :: tail ->
        %% double-quote
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }

      | 39 :: tail ->
        %% apostrophe
        {
	 (value, tail) <- parse_EntityValue start;
	 return (Value value, tail)
	 }

      | _ ->
	{
	 (ext_id, tail) <- parse_ExternalID start;
	 return (External ext_id, tail)
	 }

  %% -------------------------------------------------------------------------------------------------
  %%   [76]  NDataDecl      ::=  S 'NDATA' S Name
  %% -------------------------------------------------------------------------------------------------

  def parse_NDataDecl (start : UChars) : Possible NDataDecl =
    {
     (w1, tail) <- parse_WhiteSpace start;
     case tail of

       | 78 :: 68 :: 65 :: 84 :: 65 :: tail ->
         %% 'NDATA'
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

  %% -------------------------------------------------------------------------------------------------
  %%  [K27]  ExternalID     ::=  GenericID
  %%                                                             [KWFC: External ID]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: External ID]                           [K27] *[75] -- well_formed_external_id?
  %%
  %%    ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral
  %% -------------------------------------------------------------------------------------------------

  def parse_ExternalID (start : UChars) : Required ExternalID =
    {
     (id, tail) <- parse_GenericID start;
     (when (~ (well_formed_external_id? id))
      (error {kind        = Syntax,
	      requirement = "ExternalID     ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral",
	      start       = start,
	      tail        = tail,
	      peek        = 10,
	      we_expected = [("'SYSTEM \"...\"'",         "id with system literal"),
			     ("'PUBLIC \"...\" \"...\"'", "id with public literal and system literal")],
	      but         = "the generic ID does not contain a system literal",
	      so_we       = "pretend this is ok"}));
     return (id, tail)
    }

  %% -------------------------------------------------------------------------------------------------
  %%  [K28]  GenericID      ::=  'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral (S SystemLiteral)?
  %% -------------------------------------------------------------------------------------------------

  def parse_GenericID (start : UChars) : Required GenericID =
    case start of

      | 83 :: 89 :: 83 :: 84 :: 69 :: 77 :: tail ->
        %% 'SYSTEM'
        {
	 (w2,     tail) <- parse_WhiteSpace tail;
	 (syslit, tail) <- parse_SystemLiteral tail;
	 return ({w1     = null_whitespace,
		  public = None,
		  w2     = w2,
		  system = Some syslit},
		 tail)
	}

      | 80 :: 85 :: 66 :: 76 :: 73 :: 67 :: tail ->
        %% 'PUBLIC'
	{
	 (w1,     tail) <- parse_WhiteSpace   tail;
	 (publit, tail) <- parse_PubidLiteral tail;
	 (w2,     tail) <- parse_WhiteSpace   tail;
	 case tail of

	   | 62 :: tail ->
             %% '>'
	     return ({w1     = w1,
		      public = Some publit,
		      w2     = null_whitespace,
		      system = None},
		     tail)
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
	hard_error {kind        = Syntax,
		    requirement = "ID reference in DTD must start with 'SYSTEM' or 'PUBLIC'.",
		    start       = start,
		    tail        = start,
		    peek        = 10,
		    we_expected = [("'SYSTEM'", "system ID"),
				   ("'PUBLIC'", "public ID")],
		    but         = "something else was seen",
		    so_we       = "fail immediately"}

  %% -------------------------------------------------------------------------------------------------
  %%  [K29]  NotationDecl   ::=  '<!NOTATION' S Name S GenericID S? '>'
  %% -------------------------------------------------------------------------------------------------

  def parse_NotationDecl (start : UChars) : Required NotationDecl =
    %%
    %% We begin just past '<!NOTATION' in rule [K30], looking for:
    %%
    %%  S Name S GenericID S? '>'
    %%
    {
     (w1,   tail) <- parse_WhiteSpace start;
     (name, tail) <- parse_Name       tail;
     (w2,   tail) <- parse_WhiteSpace tail;
     (id,   tail) <- parse_GenericID  tail;  % (ExternalID | PublicID)
     (w3,   tail) <- parse_WhiteSpace tail;
     case tail of

       | 62 :: tail ->
         %% '>'
         return ({w1   = w1,
		  name = name,
		  w2   = w2,
		  id   = id,
		  w3   = w3},
		 tail)

       | char :: _ ->
	 {
	  error {kind        = Syntax,
		 requirement = "Notation Decl in DTD must terminate with '>'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("'>'", "to terminate Notation Decl")],
		 but         = (describe_char char) ^ " was seen instead",
		 so_we       = "pretend interpolated '>' was seen"};
	  return ({w1   = w1,
		   name = name,
		   w2   = w2,
		   id   = id,
		   w3   = w3},
		  tail)
	 }

       | _ ->
	 hard_error {kind        = EOF,
		     requirement = "Notation Decl in DTD must terminate with '>'.",
		     start       = start,
		     tail        = [],
		     peek        = 0,
		     we_expected = [("'>'", "to terminate Notation Decl")],
		     but         = "EOF was seen first",
		     so_we       = "fail immediately"}
	 }

endspec
