(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec

  import Parse_Literals

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

  def parse_WhiteSpace (start : UChars) : Required WhiteSpace =
    let
       def probe (tail, rev_whitespace) =
	 case tail of

	   | char :: scout ->
	     if white_char? char then
	       probe (scout, char::rev_whitespace)
	     else
	       return (reverse rev_whitespace,
		       tail)

	   | _ ->
	     return (reverse rev_whitespace,
		     tail)

    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%  [14]  CharData  ::=  [^<&]* - ([^<&]* ']]>' [^<&]*)
  %% -------------------------------------------------------------------------------------------------

  def parse_XCharData (start : UChars) : CharData * UChars =
    let
       def probe (tail, rev_char_data) =
	 case tail of

	   | 93 :: 93 :: 62 :: _ ->
	     %% ']]>'
	     (reverse rev_char_data, tail)

	   | char :: scout ->
	     if char_data_char? char then
	       %% note that char_data_char? is false for 60 ('<') and 38 ('&')
	       probe (scout, char::rev_char_data)
	     else
	       (reverse rev_char_data,
		tail)

	   | _ ->
	     (reverse rev_char_data,
	      tail)
    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%  [15]  Comment   ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
  %% -------------------------------------------------------------------------------------------------

  def parse_Comment (start : UChars) : Required Comment	=
    %% assumes we're past initial '<!--'
    let
       def probe (tl, rev_comment) =
	 case tl of

	   | 45 :: 45 :: scout ->
	     %% '--'
	     (case scout of

		| 62 :: tl ->
		  %% '-->'
		  return (reverse rev_comment,
			  tl)

		| _ ->
		  {
		   error {kind        = Syntax,
			  requirement = "'--' may not appear in a comment.",
			  start       = start,
			  tail        = tl,
			  peek        = 10,
			  we_expected = [("'>'",   "remainder of '-->', to end comment")],
			  but         = "'--' appears inside a comment",
			  so_we       = "leave the bogus '--' in the comment"};
		   probe (tail tl, 45::45::rev_comment)
		   })

	   | [] ->
	     hard_error {kind        = EOF,
			 requirement = "A comment must terminate with '-->'.",
			 start       = start,
			 tail        = start,
			 peek        = 0,
			 we_expected = [("'-->'",   "end of comment")],
			 but         = "EOF occurred first",
			 so_we       = "fail immediately"}

	   | char :: tl ->
	     probe (tl, char::rev_comment)

    in
      probe (start, [])

  %% -------------------------------------------------------------------------------------------------
  %%  [18]  CDSect    ::=  CDStart CData CDEnd
  %%  [19]  CDStart   ::=  '<![CDATA['
  %%  [20]  CData     ::=  (Char* - (Char* ']]>' Char*))
  %%  [21]  CDEnd     ::=  ']]>'
  %% -------------------------------------------------------------------------------------------------

  def parse_CDSect (start : UChars) : Required CDSect =
    %% assumes we're past "<![CDATA["
    let
       def probe (tail, rev_comment) =
	 case tail of

	   | 93 :: 93 :: 62 :: tail ->
	     %% ']]>'
	     return ({cdata = reverse rev_comment},
		     tail)

	   | [] ->
	     hard_error {kind        = EOF,
			 requirement = "A CDSect must terminate with ']]>'.",
			 start       = start,
			 tail        = start,
			 peek        = 0,
			 we_expected = [("']]>'",   "end of CDSect")],
			 but         = "EOF occurred first",
			 so_we       = "fail immediately"}

	   | char :: tail ->
	     probe (tail, char::rev_comment)
    in
      probe (start, [])

endspec
