
XML qualifying spec

  import Parse_Literals

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Character_Data                                                                      %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*
  %%
  %% [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %%
  %% [16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>' 
  %%
  %% [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%
  %% [18]  CDSect    ::=  CDStart CData CDEnd 
  %%
  %% [19]  CDStart   ::=  '<![CDATA[' 
  %%
  %% [20]  CData     ::=  (Char* - (Char* ']]>' Char*)) 
  %%
  %% [21]  CDEnd     ::=  ']]>'
  %%
  %% ----------------------------------------------------------------------------------------------------


  %% ----------------------------------------------------------------------------------------------------
  %% [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %% ----------------------------------------------------------------------------------------------------

  op parse_CharData : UChars -> (Option CharData) * UChars 
  def parse_CharData (start : UChars) : (Option CharData) * UChars =
    let 
       def probe (tail, reversed_char_data) =
	 case tail of
	   | 60             (* < *)   :: _ -> (Some (rev reversed_char_data), tail)
	   | 38             (* & *)   :: _ -> (Some (rev reversed_char_data), tail)
	   | 93 :: 93 :: 62 (* ]]> *) :: _ -> (Some (rev reversed_char_data), tail)	
	   | char :: scout -> 
	     probe (scout, cons (char, reversed_char_data))
	   | _ ->
	     (Some (rev reversed_char_data),
	      tail)
    in
      probe (start, [])

  %% ----------------------------------------------------------------------------------------------------
  %% [18]  CDSect  ::=  CDStart CData CDEnd 
  %% [19]  CDStart ::=  '<![CDATA[' 
  %% [20]  CData   ::=  (Char* - (Char* ']]>' Char*)) 
  %% [21]  CDEnd   ::=  ']]>'
  %% ----------------------------------------------------------------------------------------------------

  op parse_CDSect : UChars -> Required CDSect
  op parse_Comment : UChars -> Required Comment
endspec
