XML qualifying spec

  import Parse_ElementTag

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          External                                                                            %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% 
  %% *[77]  TextDecl            ::=  '<?xml' VersionInfo? EncodingDecl S? '?>'
  %%   ==>
  %% [K13]  TextDecl            ::=  ElementTag
  %%
  %%                                                             [KC: Proper Text Decl]
  %%  
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def parse_TextDecl (start : UChars) : Possible TextDecl =
    {
     (possible_tag, tail) <- parse_Option_ElementTag start;
     case possible_tag of
       | None -> 
         hard_error {kind        = Syntax,
		     requirement = "Expected an external text header decl.",
		     start       = start,
		     tail        = tail,
		     peek        = 50,
		     we_expected = [("'<?xml' VersionInfo? EncodingDecl S? '?>'", "A legal external text header decl")],
		     but         = "we didn't even get a plausible declaration",
		     so_we       = "fail immediately"}
       | Some tag ->
         {
	  (when (~ ((tag.prefix = (ustring "?")) & (tag.name = (ustring "xml")) & (tag.postfix = (ustring "?"))))
	   (error {kind        = Syntax,
		   requirement = "an external text header decl should begin with '<?xml' and end with '?>'.",
		   start       = start,
		   tail        = tail,
		   peek        = 50,
		   we_expected = [("'<?xml' VersionInfo? EncodingDecl S? '?>'", "A legal external text header decl")],
		   but         = "the observed xml decl differs from that pattern",
		   so_we       = "proceed as if the external text decl was well-formed"}));
	  (saw_version?, saw_encoding?) <-
	  (foldM (fn (saw_version?, saw_encoding?) -> fn attribute -> 
		    case attribute.name of
	              | 118 :: 101 :: 114 :: 115 :: 105 :: 111 :: 110 :: [] (* 'version' *) ->
		        {
			 (when saw_version? 
			  (error {kind        = WFC,
				  requirement = "There should be at most one version attribute in an external text header decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple version attributes were seen",
				  so_we       = "leave duplicate version attributes in the external text header decl"}));
			 (when saw_encoding? 
			  (error {kind        = WFC,
				  requirement = "The version attribute (if any) must come first in an external text header decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "a version attribute follows an encoding attribute in an external text header decl",
				  so_we       = "leave the mis-ordered attributes in the external text header decl"}));
			 return (true, saw_encoding?)
			 }
		      | 101 :: 110 :: 99 :: 111 :: 100 :: 105 :: 110 :: 103 :: [] (* 'encoding' *) ->
		        {
			 (when saw_encoding? 
			  (error {kind        = WFC,
				  requirement = "At most one encoding attributes is allowed in an external text header decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [],
				  but         = "multiple encoding attributes were seen in an external text header decl",
				  so_we       = "leave duplicate encoding attributes in the external text header decl"}));
			 return (saw_version?, true)
			 }
		      | uname ->
			{
			 (when true
			  (error {kind        = WFC,
				  requirement = "Only version and encoding attributes are allowed in an external text header decl.",
				  start       = start,
				  tail        = tail,
				  peek        = 0,
				  we_expected = [("version='1.0'",       "version attribute"),
						 ("encoding='...'",      "encoding attribute")],
				  but         = "unrecognized attribute [" ^ (string uname) ^ "] was seen in an external text header decl",
				  so_we       = "leave that unrecognized attribute in the external text header decl"}));
			 return (saw_version?, saw_encoding?)
			 })
	          (false, false)
		  tag.attributes);

	  (when (~ saw_encoding?)
	   (error {kind        = WFC,
		   requirement = "An encoding attribute is required in every external text header decl.",
		   start       = start,
		   tail        = tail,
		   peek        = 0,
		   we_expected = [("encoding='...'",  "encoding attribute")],
		   but         = "no encoding attribute was seen in an external text header decl",
		   so_we       = "proceed with the encoding attribute missing"}));
	  return (Some tag, tail)
	 }}

endspec