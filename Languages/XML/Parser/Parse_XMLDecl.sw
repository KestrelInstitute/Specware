XML qualifying spec

  import Parse_ElementTag

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XMLDecl                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% *[23]  XMLDecl       ::=  '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
  %%   ==>
  %% [K14]  XMLDecl       ::=  ElementTag
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

  %% -------------------------------------------------------------------------------------------------
  %% 
  %% [K14]  XMLDecl       ::=  ElementTag
  %%                                                             [KC: Proper XML Decl]
  %%                                                             [VC: Standalone Document Declaration]
  %% 
  %% -------------------------------------------------------------------------------------------------

  def parse_XMLDecl (start : UChars) : Required XMLDecl =
    {
     (possible_tag, tail) <- parse_Option_ElementTag start;
     case possible_tag of
       | None -> 
         hard_error {kind        = Syntax,
		     requirement = "Expected an xml header decl.",
		     problem     = "Didn't even get a plausible declaration.",
		     expected    = [("'<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'", "A legal xml header decl")],
		     start       = start,
		     tail        = tail,
		     peek        = 50,
		     action      = "immediate failure"}
       | Some tag ->
         {
	  (when (~ ((tag.prefix = (ustring "?")) & (tag.name = (ustring "xml"))))
	   (error {kind        = Syntax,
		   requirement = "An xml header decl should begin with '<?xml'.",
		   problem     = "Observed decl begins '<" ^ (string tag.prefix) ^ (string tag.name) ^ "'.",
		   expected    = [("'<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'", "A legal xml header decl")],
		   start       = start,
		   tail        = tail,
		   peek        = 50,
		   action      = "proceed as if xml decl was well-formed"}));
	  (saw_version?, saw_encoding?, saw_standalone?) <-
	  (foldM (fn (saw_version?, saw_encoding?, saw_standalone?) -> fn attribute -> 
		    case attribute.name of
	              | 118 :: 101 :: 114 :: 115 :: 105 :: 111 :: 110 (* 'version' *) :: [] ->
		        {
			 (when saw_version? 
			  (error {kind        = WFC,
				  requirement = "There should be exactly one version attribute in an xml header decl.",
				  problem     = "Multiple version attributes were seen.",
				  expected    = [],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave duplicate version attributes in xml header decl"}));
			 (when saw_encoding? 
			  (error {kind        = WFC,
				  requirement = "The version attribute must come first in an xml header decl.",
				  problem     = "A version attribute follows an encoding attribute in an xml header decl.",
				  expected    = [],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave out of order in xml header decl"}));
			 (when saw_standalone? 
			  (error {kind        = WFC,
				  requirement = "The version attribute must come first in an xml header decl.",
				  problem     = "A version attribute follows a standalone attribute in an xml header decl.",
				  expected    = [],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave out of order in xml header decl"}));
			 return (true, saw_encoding?, saw_standalone?)
			 }
		      | 101 :: 110 :: 99 :: 111 :: 100 :: 105 :: 110 :: 103 (* 'encoding' *) :: [] ->
		        {
			 (when saw_encoding? 
			  (error {kind        = WFC,
				  requirement = "At most one encoding attributes is allowed in an xml header decl.",
				  problem     = "Multiple encoding attributes were seen in an xml header decl.",
				  expected    = [],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave duplicate encoding attributes in xml header decl"}));
			 (when saw_standalone? 
			  (error {kind        = WFC,
				  requirement = "Any encoding attribute must preceed a standalone attribute in an xml header decl.",
				  problem     = "An encoding attribute follows a standalone attribute in an xml header decl.",
				  expected    = [],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave out of order in xml header decl"}));
			 return (saw_version?, true, saw_standalone?)
			 }
		      | 115 :: 116 :: 97 :: 110 :: 100 :: 97 :: 108 :: 111 :: 110 :: 101 (* 'standalone' *) :: [] ->
			{
			 (when saw_standalone? 
			  (error {kind        = WFC,
				  requirement = "At most one standalone attributes is allowed in an xml header decl.",
				  problem     = "Multiple standalone attributes were seen in an xml header decl.",
				  expected    = [],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave duplicate standalone attributes in xml header decl"}));
			 return (saw_version?, saw_encoding?, true)
			}
		      | uname ->
			{
			 (when true
			  (error {kind        = WFC,
				  requirement = "Only version, encoding, and standalone attributes are allowed in an xml header decl.",
				  problem     = "Unrecognized attribute [" ^ (string uname) ^ "] was seen in an xml header decl.",
				  expected    = [("version='1.0'",       "version attribute"),
						 ("encoding='...",       "encoding attribute"),
						 ("standalone='yes/no'", "standalone attribute")],
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  action      = "leave unrecognized attribute in xml header decl"}));
			 return (saw_version?, saw_encoding?, saw_standalone?)
			 })
	          (false, false, false)
		  tag.attributes);

	  (when (~ saw_version?)
	   (error {kind        = WFC,
		   requirement = "A version attribute is required in every xml header decl.",
		   problem     = "No version attribute was seen in an xml header decl.",
		   expected    = [("version='...",  "version attribute")],
		   start       = start,
		   tail        = tail,
		   peek        = 0,
		   action      = "proceed with attribute missing"}));
	  
	  (when (~ (tag.postfix = ustring "?"))
	   (error {kind        = Syntax,
		   requirement = "An xml header decl should end with '?>'.",
		   problem     = "An xml header decl ends with " ^ (string tag.postfix) ^ ">'",
		   expected    = [("'?>'",  "to end '<?xml ...>' decl")],
		   start       = start,
		   tail        = tail,
		   peek        = 0,
		   action      = "proceed as if decl terminated correctly"}));
	  return (tag, tail)
	 }}

endspec