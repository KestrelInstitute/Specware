XML qualifying spec

  import Parse_GenericTag

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          XMLDecl                                                                             %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% *[23]  XMLDecl       ::=  '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
  %%   ==>
  %% [K14]  XMLDecl       ::=  GenericTag
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
  %% [K14]  XMLDecl       ::=  GenericTag
  %%                                                             [KC: Proper XML Decl]
  %%                                                             [VC: Standalone Document Declaration]
  %% 
  %% -------------------------------------------------------------------------------------------------

  def parse_XMLDecl (start : UChars) : Required XMLDecl =
    {
     (possible_tag, tail) <- parse_Option_GenericTag start;
     case possible_tag of
       | None -> error ("Expected xml decl", start, tail)
       | Some tag ->
         {
	  (when (~ ((tag.prefix = (ustring "?")) & (tag.name = (ustring "xml"))))
	   (error ("WFC: XML decl should begin '<?xml', not '<" ^ (string tag.prefix) ^ (string tag.name),
		   start, tail)));
	  (saw_version?, saw_encoding?, saw_standalone?) <-
	  (foldM (fn (saw_version?, saw_encoding?, saw_standalone?) -> fn attribute -> 
		    case attribute.name of
	              | 118 :: 101 :: 114 :: 115 :: 105 :: 111 :: 110 (* 'version' *) :: [] ->
		        {
			 (when saw_version? 
			  (error ("WFC: Multiple version attributes in XML decl", start, tail)));
			 (when saw_encoding? 
			  (error ("WFC: version attribute follows encoding attribute in XML decl", start, tail)));
			 (when saw_standalone? 
			  (error ("WFC version attribute follows standalone attribute in XML decl", start, tail)));
			 return (true, saw_encoding?, saw_standalone?)
			 }
		      | 101 :: 110 :: 99 :: 111 :: 100 :: 105 :: 110 :: 103 (* 'encoding' *) :: [] ->
		        {
			 (when saw_encoding? 
			  (error ("WFC Multiple encoding attributes in XML decl", start, tail)));
			 (when saw_standalone? 
			  (error ("WFC encoding attribute follows standalone attribute in XML decl", start, tail)));
			 return (saw_version?, true, saw_standalone?)
			 }
		      | 115 :: 116 :: 97 :: 110 :: 100 :: 97 :: 108 :: 111 :: 110 :: 101 (* 'standalone' *) :: [] ->
			{
			 (when saw_encoding? 
			  (error ("WFC Multiple standalone attributes in XML decl", start, tail)));
			 (when saw_standalone? 
			  (error ("WFC encoding attribute follows standalone attribute in XML decl", start, tail)));
			 return (saw_version?, saw_encoding?, true)
			}
		      | uname ->
			{
			 (when true
			  (error ("WFC Unrecognized attribute [" ^ (string uname) ^ "] in XML decl", start, tail)));
			 return (saw_version?, saw_encoding?, saw_standalone?)
			 })
	          (false, false, false)
		  tag.attributes);

	  (when (~ saw_version?)
	   (error ("WFC No version attribute in XML decl", start, tail)));
	    
	  (when (~ (tag.postfix = ustring "?"))
	   (error ("WFC XML decl should end with '?>', not '" ^ (string tag.postfix) ^ ">'", start, tail)));

	  return (tag, tail)
	 }}

endspec