
XML qualifying spec

  import Parse_Literals

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          Character_Data                                                                      %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %%
  %% [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %%
  %% [18]  CDSect    ::=  CDStart CData CDEnd 
  %% [19]  CDStart   ::=  '<![CDATA[' 
  %% [20]  CData     ::=  (Char* - (Char* ']]>' Char*)) 
  %% [21]  CDEnd     ::=  ']]>'
  %%
  %% ----------------------------------------------------------------------------------------------------

  def parse_WhiteSpace (start : UChars) : Required WhiteSpace =
    let
       def probe (tail, rev_whitespace) =
	 case tail of
	   | char :: scout ->
	     if white_char? char then
	       probe (scout, cons (char, rev_whitespace))
	     else
	       return (rev rev_whitespace,
		       tail)
	   | _ ->
	     return (rev rev_whitespace,
		     tail)
    in
      probe (start, [])

  %% ----------------------------------------------------------------------------------------------------

  def parse_CharData (start : UChars) : (Option CharData) * UChars =
    let 
       def probe (tail, reversed_char_data) =
	 case tail of
	   | 93 :: 93 :: 62 (* ]]> *) :: _ -> (Some (rev reversed_char_data), tail)	
	   | char :: scout -> 
	     if char_data_char? char then
	       %% note that char_data_char? is false for 60 (* < *) and 38 (* & *) 
	       probe (scout, cons (char, reversed_char_data))
	     else
	       (Some (rev reversed_char_data),
		tail)
	   | _ ->
	     (Some (rev reversed_char_data),
	      tail)
    in
      probe (start, [])

  %% ----------------------------------------------------------------------------------------------------

  def parse_Comment (start : UChars) : Required Comment	=
    %% assumes we're past initial '<!--'
    let
       def probe (tail, rev_comment) =
	 case tail of
	   | 45 :: 45 (* '--' *) :: scout ->
	     (case scout of
		| 62  (* '>' *) :: tail ->
		  return (rev rev_comment, 
			  tail)
		| _ ->
		  {
		   error ("Double dash inside comment", start, tail);
		   probe (tl tail, cons (45, rev_comment))
		   })
	   | [] ->
	     error ("EOF inside comment", start, tail)
	   | char :: tail ->
	     probe (tail, cons (char, rev_comment))
    in
      probe (start, [])

  %% ----------------------------------------------------------------------------------------------------

  def parse_CDSect (start : UChars) : Required CDSect =
    %% parse_CDSECT assumes we're past "<![CDATA["
    let
       def probe (tail, rev_comment) =
	 case tail of
	   | 93 :: 93 :: 62 (* ']]>' *) :: tail ->
	     return ({cdata = rev rev_comment}, 
		     tail)
	   | [] ->
	     error ("EOF inside CDSect", start, tail)
	   | char :: tail ->
	     probe (tail, cons (char, rev_comment))
    in
      probe (start, [])

endspec
