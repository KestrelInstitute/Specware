(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import Parse_ElementTag

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

  def parse_XMLDecl (start : UChars) : Possible XMLDecl =
    {
     (possible_tag, tail) <- parse_Option_ElementTag start;
     case possible_tag of
       | None ->
         return (None, start)
       | Some tag ->
	 %% [KWFC: XML Decl]
	 if well_formed_xml_decl? tag then
	   return (Some tag, tail)
	 else if (~ ((tag.prefix = (ustring "?")) && (tag.name = (ustring "xml")))) then
	   return (None, start)
         else
	   %% Tag starts with '<?xml', but isn't a legal xml decl.  Find out why.
	   {
	    (saw_version?, _, _) <-
	    (foldM (fn (saw_version?, saw_encoding?, saw_standalone?) -> fn attribute ->
		    case attribute.name of
	              | 118 :: 101 :: 114 :: 115 :: 105 :: 111 :: 110 :: [] ->
		        %% 'version'
		        {
			 (when saw_version?
			  (error {kind        = WFC,
				  requirement = "There should be exactly one version attribute in the 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple version attributes were seen",
				  so_we       = "leave duplicate version attributes in the 'xml' decl"}));
			 (when saw_encoding?
			  (error {kind        = WFC,
				  requirement = "The version attribute must come first in the 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "a version attribute follows an encoding attribute in the 'xml' decl",
				  so_we       = "leave the mis-ordered attributes in the 'xml' decl"}));
			 (when saw_standalone?
			  (error {kind        = WFC,
				  requirement = "The version attribute must come first in an 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "a version attribute follows a standalone attribute in the 'xml' decl",
				  so_we       = "leave the mis-ordered attributes in the 'xml' decl"}));
			 return (true, saw_encoding?, saw_standalone?)
			 }
		      | 101 :: 110 :: 99 :: 111 :: 100 :: 105 :: 110 :: 103 :: [] ->
			%% 'encoding'
		        {
			 (when saw_encoding?
			  (error {kind        = WFC,
				  requirement = "At most one encoding attributes is allowed in the 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple encoding attributes were seen in the 'xml' decl",
				  so_we       = "leave duplicate encoding attributes in the 'xml' decl"}));
			 (when saw_standalone?
			  (error {kind        = WFC,
				  requirement = "Any encoding attribute must preceed a standalone attribute in the 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "an encoding attribute follows a standalone attribute in the 'xml' decl",
				  so_we       = "leave the mis-ordered attributes in the 'xml' decl"}));
			 return (saw_version?, true, saw_standalone?)
			 }

		      | 115 :: 116 :: 97 :: 110 :: 100 :: 97 :: 108 :: 111 :: 110 :: 101 :: [] ->
			%% 'standalone'
			{
			 (when saw_standalone?
			  (error {kind        = WFC,
				  requirement = "At most one standalone attributes is allowed in the 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple standalone attributes were seen int the 'xml' decl",
				  so_we       = "leave duplicate standalone attributes in the 'xml' decl"}));
			 return (saw_version?, saw_encoding?, true)
			}

		      | uname ->
			{
			 (when true
			  (error {kind        = WFC,
				  requirement = "Only version, encoding, and standalone attributes are allowed in the 'xml' decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [("version='1.0'",       "version attribute"),
						 ("encoding='...",       "encoding attribute"),
						 ("standalone='yes/no'", "standalone attribute")],
				  but         = "unrecognized attribute [" ^ (string uname) ^ "] was seen in the 'xml' decl",
				  so_we       = "leave that unrecognized attribute in the 'xml' decl"}));
			 return (saw_version?, saw_encoding?, saw_standalone?)
			 })
	          (false, false, false)
		  tag.attributes);

	  (when (~ saw_version?)
	   (error {kind        = WFC,
		   requirement = "A version attribute is required in the 'xml' decl.",
		   start       = start,
		   tail        = tail,
		   peek        = 0,
		   we_expected = [("version='...",  "version attribute")],
		   but         = "no version attribute was seen in the 'xml' decl",
		   so_we       = "proceed with the version attribute missing"}));

	  (when (~ (tag.postfix = ustring "?"))
	   (error {kind        = Syntax,
		   requirement = "The 'xml' decl should end with '?>'.",
		   start       = start,
		   tail        = tail,
		   peek        = 0,
		   we_expected = [("'?>'",  "to end '<?xml ...>' decl")],
		   but         = "The 'xml' decl ends with " ^ (string tag.postfix) ^ ">'",
		   so_we       = "proceed as if the 'xml' decl terminated correctly"}));
	  return (Some tag, tail)
	 }}

  %% -------------------------------------------------------------------------------------------------
  %%   [K4]  TextDecl      ::=  ElementTag
  %%                                                             [KWFC: Text Decl]
  %% -------------------------------------------------------------------------------------------------
  %%  [KWFC: Text Decl]                             [K4] *[77]  -- well_formed_text_decl?
  %%
  %%    TextDecl  ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %% -------------------------------------------------------------------------------------------------

  def parse_TextDecl (start : UChars) : Possible TextDecl =
    {
     (possible_tag, tail) <- parse_Option_ElementTag start;
     case possible_tag of
       | None ->
         return (None, start)
       | Some tag ->
	 %% [KWFC: Text Decl]
	 if well_formed_text_decl? tag then
	   return (Some tag, tail)
	 else if (~ ((tag.prefix = (ustring "?")) && (tag.name = (ustring "xml")))) then
	   return (None, start)
         else
	   %% Tag starts with '<?xml', but isn't a legal text decl.  Find out why.
	   {
	    (saw_version?, saw_encoding?) <-
	    (foldM (fn (saw_version?, saw_encoding?) -> fn attribute ->
		    case attribute.name of
		      | 118 :: 101 :: 114 :: 115 :: 105 :: 111 :: 110 :: [] ->
		        %% 'version'
		        {
			 (when saw_version?
			  (error {kind        = WFC,
				  requirement = "There should be at most one version attribute in a text decl (external 'xml' decl).",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple version attributes were seen",
				  so_we       = "leave duplicate version attributes in the text decl"}));
			 (when saw_encoding?
			  (error {kind        = WFC,
				  requirement = "The version attribute (if any) must come first in a text decl (external 'xml' decl).",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "a version attribute follows an encoding attribute in a text decl",
				  so_we       = "leave the mis-ordered attributes in the text decl"}));
			 return (true, saw_encoding?)
			}
		      | 101 :: 110 :: 99 :: 111 :: 100 :: 105 :: 110 :: 103 :: [] ->
			%% 'encoding'
			{
			 (when saw_encoding?
			  (error {kind        = WFC,
				  requirement = "At most one encoding attributes is allowed in a text decl (external 'xml' decl).",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple encoding attributes were seen in a text decl",
				  so_we       = "leave duplicate encoding attributes in the text decl"}));
			 return (saw_version?, true)
			}
		      | uname ->
			{
			 (when true
			  (error {kind        = WFC,
				  requirement = "Only version and encoding attributes are allowed in a text decl (external 'xml' decl).",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [("version='1.0'",       "version attribute"),
						 ("encoding='...'",      "encoding attribute")],
				  but         = "unrecognized attribute [" ^ (string uname) ^ "] was seen in a text decl",
				  so_we       = "leave that unrecognized attribute in the text decl"}));
			 return (saw_version?, saw_encoding?)
			})
	           (false, false)
		   tag.attributes);

	    (when (~ saw_encoding?)
	     (error {kind        = WFC,
		     requirement = "An encoding attribute is required in every text decl (external 'xml' decl).",
		     start       = start,
		     tail        = tail,
		     peek        = 0,
		     we_expected = [("encoding='...'",  "encoding attribute")],
		     but         = "no encoding attribute was seen in a text decl",
		     so_we       = "proceed with the encoding attribute missing"}));

	    (when (~ (tag.postfix = ustring "?"))
	     (error {kind        = Syntax,
		     requirement = "A text decl (external 'xml' decl) should end with '?>'.",
		     start       = start,
		     tail        = tail,
		     peek        = 0,
		     we_expected = [("'?>'",  "to end '<?xml ...>' decl")],
		     but         = "a text decl ends with " ^ (string tag.postfix) ^ ">'",
		     so_we       = "proceed as if that text decl terminated correctly"}));
	    return (Some tag, tail)
	   }}

endspec
