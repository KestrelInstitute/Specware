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
         hard_error (Surprise {context = "Expected xml decl",
			       expected = [("<?xml ...?>", "A legal xml decl")],
			       action   = "Immediate failure",
			       start    = start,
			       tail     = tail,
			       peek     = 50})
       | Some tag ->
         {
	  (when (~ ((tag.prefix = (ustring "?")) & (tag.name = (ustring "xml"))))
	   (error (WFC {description = "XML decl should begin '<?xml', not '<" ^ (string tag.prefix) ^ (string tag.name)})));
	  (saw_version?, saw_encoding?, saw_standalone?) <-
	  (foldM (fn (saw_version?, saw_encoding?, saw_standalone?) -> fn attribute -> 
		    case attribute.name of
	              | 118 :: 101 :: 114 :: 115 :: 105 :: 111 :: 110 (* 'version' *) :: [] ->
		        {
			 (when saw_version? 
			  (error (WFC {description = "Multiple version attributes in XML decl"})));
			 (when saw_encoding? 
			  (error (WFC {description = "version attribute follows encoding attribute in XML decl"})));
			 (when saw_standalone? 
			  (error (WFC {description = "version attribute follows standalone attribute in XML decl"})));
			 return (true, saw_encoding?, saw_standalone?)
			 }
		      | 101 :: 110 :: 99 :: 111 :: 100 :: 105 :: 110 :: 103 (* 'encoding' *) :: [] ->
		        {
			 (when saw_encoding? 
			  (error (WFC {description = "Multiple encoding attributes in XML decl"})));
			 (when saw_standalone? 
			  (error (WFC {description = "encoding attribute follows standalone attribute in XML decl"})));
			 return (saw_version?, true, saw_standalone?)
			 }
		      | 115 :: 116 :: 97 :: 110 :: 100 :: 97 :: 108 :: 111 :: 110 :: 101 (* 'standalone' *) :: [] ->
			{
			 (when saw_encoding? 
			  (error (WFC {description = "Multiple standalone attributes in XML decl"})));
			 (when saw_standalone? 
			  (error (WFC {description = "encoding attribute follows standalone attribute in XML decl"})));
			 return (saw_version?, saw_encoding?, true)
			}
		      | uname ->
			{
			 (when true
			  (error (WFC {description = "Unrecognized attribute [" ^ (string uname) ^ "] in XML decl"})));
			 return (saw_version?, saw_encoding?, saw_standalone?)
			 })
	          (false, false, false)
		  tag.attributes);

	  (when (~ saw_version?)
	   (error (WFC {description = "No version attribute in XML decl"})));
	    
	  (when (~ (tag.postfix = ustring "?"))
	   (error (WFC {description = "XML decl should end with '?>', not '" ^ (string tag.postfix) ^ ">'"})));

	  return (tag, tail)
	 }}

endspec