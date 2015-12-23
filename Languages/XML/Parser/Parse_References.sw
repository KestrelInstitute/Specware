(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec

  import Parse_Names

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

  def parse_CharRef (start : UChars, tail : UChars) : Required Reference =
    %%
    %%  We begin just past the '&#' in rule [66] looking for one of:
    %%
    %%     'x' [0-9a-fA-F]+ ';'
    %%         [0-9]+       ';'
    %%
    case tail of
      | 120 (* 'x' *) :: tail -> parse_char_ref (start, tail,  parse_hex,     Hex,     "Hex")
      | _                     -> parse_char_ref (start, start, parse_decimal, Decimal, "Decimal")

  def parse_char_ref (start  : UChars,
		      tail   : UChars,
		      parser : UChars -> Required Nat,
		      style  : NumberBase,
		      desc   : String)
    : Required Reference =
    {
     (char, tail) <- parser tail;
     (when (~ (char? char))
      (error {kind        = WFC,
	      requirement = "Characters referred to using character references must match the production for Char.",
	      start       = start,
	      tail        = tail,
	      peek        = 0,
	      we_expected = [("<see doc>", desc ^ " code for legal XML Char")],
	      but         = (describe_char char) ^ "is not an XML Char",
	      so_we       = "pass along the bogus character"}));
     case tail of

       | 59 :: tail ->
         %% ';'
         return (Char {style = style,
		       char  = char},
		 tail)

       | char :: _ ->
	 {
	  error {kind        = Syntax,
		 requirement = desc ^ " character references must terminate with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of " ^ desc ^ "character reference")],
		 but         = (describe_char char) ^ " occurred first",
		 so_we       = "pretend interpolated ';' was seen."};
	  return (Char {style = style,
			char  = char},
		  tail)
		  }

       | _ ->
	 {
	  error {kind        = EOF,
		 requirement = desc ^ " character references must terminate with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of " ^ desc ^ " character reference")],
		 but         = "EOF occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return (Char {style = style,
			char  = char},
		  tail)
	 }}


  def parse_decimal (start : UChars) : Required UChar =
   let
      def probe (tail, n) =
	case tail of
	  |  48 (* '0' *) :: tail -> probe (tail, 10 * n)
	  |  49 (* '1' *) :: tail -> probe (tail, 10 * n + 1)
	  |  50 (* '2' *) :: tail -> probe (tail, 10 * n + 2)
	  |  51 (* '3' *) :: tail -> probe (tail, 10 * n + 3)
	  |  52 (* '4' *) :: tail -> probe (tail, 10 * n + 4)
	  |  53 (* '5' *) :: tail -> probe (tail, 10 * n + 5)
	  |  54 (* '6' *) :: tail -> probe (tail, 10 * n + 6)
	  |  55 (* '7' *) :: tail -> probe (tail, 10 * n + 7)
	  |  56 (* '8' *) :: tail -> probe (tail, 10 * n + 8)
	  |  57 (* '9' *) :: tail -> probe (tail, 10 * n + 9)
	  | _ ->
	    if start = tail then
	      {
	       error {kind        = Syntax,
		      requirement = "A decimal number is required.",
		      start       = start,
		      tail        = tail,
		      peek        = 10,
		      we_expected = [("[0-9]+", "decimal digits")],
		      but         = "no decimal digits were seen",
		      so_we       = "pretend '88' (the decimal encoding of 'X') was seen"};
	       return (88, tail)
	       }
	    else
	       return (n, tail)
   in
     probe (start, 0)

  def parse_hex (start : UChars) : Required UChar =
   let
      def probe (tail, n) =
	case tail of
	  |  48 (* '0' *) :: tail -> probe (tail, 10 * n)
	  |  49 (* '1' *) :: tail -> probe (tail, 10 * n + 1)
	  |  50 (* '2' *) :: tail -> probe (tail, 10 * n + 2)
	  |  51 (* '3' *) :: tail -> probe (tail, 10 * n + 3)
	  |  52 (* '4' *) :: tail -> probe (tail, 10 * n + 4)
	  |  53 (* '5' *) :: tail -> probe (tail, 10 * n + 5)
	  |  54 (* '6' *) :: tail -> probe (tail, 10 * n + 6)
	  |  55 (* '7' *) :: tail -> probe (tail, 10 * n + 7)
	  |  56 (* '8' *) :: tail -> probe (tail, 10 * n + 8)
	  |  57 (* '9' *) :: tail -> probe (tail, 10 * n + 9)

	  |  65 (* 'A' *) :: tail -> probe (tail, 10 * n + 10)
	  |  66 (* 'B' *) :: tail -> probe (tail, 10 * n + 11)
	  |  67 (* 'C' *) :: tail -> probe (tail, 10 * n + 12)
	  |  68 (* 'D' *) :: tail -> probe (tail, 10 * n + 13)
	  |  69 (* 'E' *) :: tail -> probe (tail, 10 * n + 14)
	  |  70 (* 'F' *) :: tail -> probe (tail, 10 * n + 15)

	  |  97 (* 'a' *) :: tail -> probe (tail, 10 * n + 10)
	  |  98 (* 'b' *) :: tail -> probe (tail, 10 * n + 11)
	  |  99 (* 'c' *) :: tail -> probe (tail, 10 * n + 12)
	  | 100 (* 'd' *) :: tail -> probe (tail, 10 * n + 13)
	  | 101 (* 'e' *) :: tail -> probe (tail, 10 * n + 14)
	  | 102 (* 'f' *) :: tail -> probe (tail, 10 * n + 15)
	  | _ ->
	    if start = tail then
	      {
	       error {kind        = Syntax,
		      requirement = "A hex number is required.",
		      start       = start,
		      tail        = tail,
		      peek        = 10,
		      we_expected = [("[0-9A-Fa-f]+", "hex digits")],
		      but         = "no hex digits were seen",
		      so_we       = "pretend '58' (the hex encoding of 'X') was seen"};
	       return (88, tail) (* = hex 58 *)
	      }
	    else
	       return (n, tail)
   in
     probe (start, 0)

  %% -------------------------------------------------------------------------------------------------
  %%  [67]  Reference    ::=  EntityRef | CharRef
  %% -------------------------------------------------------------------------------------------------

  def parse_Reference (start : UChars) : Required Reference =
    %%
    %%  We begin just past the '&' in rules [66] and [68], looking for one of:
    %%
    %%    '#x' [0-9a-fA-F]+ ';'
    %%    '#'  [0-9]+       ';'
    %%    Name              ';'
    %%
    case start of
      | 35 (* '#' *) :: tail -> parse_CharRef   (start, tail)
      | _ :: _               -> parse_EntityRef start
      | _ ->
        hard_error {kind        = EOF,
		    requirement = "Ampersand starts some kind of reference.",
		    start       = start,
		    tail        = [],
		    peek        = 0,
		    we_expected = [("'&#x' [0-9a-fA-F]+ ';'", "Hex character reference"),
				   ("'&#'  [0-9]+       ';'", "Decimal character reference"),
				   ("'&'   Name         ';'", "Entity reference")],
		    but         = "EOF occurred first",
		    so_we       = "fail immediately"}

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

  def parse_EntityRef (start : UChars) : Required Reference =
    {
     (name, tail) <- parse_Name start;
     case tail of

       | 59 :: tail ->
         %% ';'
         return (Entity {name = name},
		 tail)

       | char :: _ ->
	 {
	  error {kind        = Syntax,
		 requirement = "Entity references must terminate with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of entity reference")],
		 but         = (describe_char char) ^ " occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return (Entity {name = name},
		  tail)
	 }
       | _ ->
	 {
	  error {kind        = EOF,
		 requirement = "Entity references must terminate with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of entity reference")],
		 but         = "EOF occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return (Entity {name = name},
		  tail)
	 }}

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

  def parse_PEReference (start : UChars) : Required PEReference =
    {
     %% We begin just past the '%", looking for:
     %%
     %%   Name ';'
     %%
     (name, tail) <- parse_Name start;
     case tail of

       | 59 :: tail ->
         %% ';'
         return ({name = name},
		 tail)

       | char :: _ ->
	 {
	  error {kind        = Syntax,
		 requirement = "PEReferences must with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of PEReference")],
		 but         = (describe_char char) ^ " occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return ({name = name},
		  tail)
	 }

       | _ ->
	 {
	  error {kind        = Syntax,
		 requirement = "PEReferences must with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of PEReference")],
		 but         = "EOF occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return ({name = name},
		  tail)
	 }}


endspec
