(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import Parse_Names              % parse_NmToken    [redundant, given Parse_Character_Strings]
  import Parse_Character_Strings  % parse_WhiteSpace

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          PI                                                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %%  [Definition: Processing instructions (PIs) allow documents to contain instructions for
  %%   applications.]
  %%
  %%  *[16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'
  %%    ==>
  %%  [K30]  PI        ::= '<?' PITarget (S PIValue)? '?>'
  %%  [K31]  PIValue   ::= Char* - (Char* '?>' Char*)
  %%
  %%   [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%  [K30]  PI        ::= '<?' PITarget (S PIValue)? '?>'
  %% -------------------------------------------------------------------------------------------------

  def parse_PI (start : UChars) : Required PI =
    %% assumes we're past initial '<?'
    {
     (target, tail) <- parse_PITarget                        start;
     (value,  tail) <- parse_Optional_WhiteSpace_and_PIValue tail;
     return ({target = target,
	      value  = value},
	     tail)
    }

  %% -------------------------------------------------------------------------------------------------
  %%   [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %% -------------------------------------------------------------------------------------------------

  def parse_PITarget (start : UChars) : Required PITarget =
    {
     (target, tail) <- parse_NmToken start;
     (when (~ (pi_target? target))
      (error {kind        = Syntax,
	      requirement = "PI name must be normal name not starting with 'xml'.",
	      start       = start,
	      tail        = tail,
	      peek        = 10,
	      we_expected = [("Name - 'xml' variants", "legal PI target name")],
	      but         = "we saw the illegal name '" ^ (string target) ^ "' instead",
	      so_we       = "pretend '" ^ (string target) ^ "' is an acceptable name"}));
     return (target, tail)
     }

  %% -------------------------------------------------------------------------------------------------
  %%  [K30]  PI        ::= '<?' PITarget (S PIValue)? '?>'
  %%  [K31]  PIValue   ::= Char* - (Char* '?>' Char*)
  %% -------------------------------------------------------------------------------------------------

  def parse_Optional_WhiteSpace_and_PIValue (start : UChars) : Possible (WhiteSpace * PIValue) =
    let
      def probe (tail, rev_result) =
	case tail of

	  | 63 :: 62 :: tail ->
	    %% '?>'
	    return (reverse rev_result,
		    tail)

	  | char :: tail ->
	    probe (tail, char::rev_result)

	  | _ ->
	    hard_error {kind        = EOF,
			requirement = "PI must terminate with '?>'.",
			start       = start,
			tail        = tail,
			peek        = 10,
			we_expected = [("'?>'", "termination of PI")],
			but         = "EOF occurred first",
			so_we       = "fail immediately"}
    in
      {
       (whitespace, tail) <- parse_WhiteSpace start;
       (pi_value,   tail) <- probe (tail, []);
       case (whitespace, pi_value) of

	 | ([], []) ->
	   return (None, start)

	 | ([], _)  ->
	   {
	    error {kind        = Syntax,
		   requirement = "PI requires whitespace between name and value.",
		   start       = start,
		   tail        = tail,
		   peek        = 10,
		   we_expected = [("( #x9 | #xA | #xD | #x20 )", "at least one character of whitespace")],
		   but         = "no whitespace was seen",
		   so_we       = "pretend some (vacuous) whitespace was seen"};
	    return (Some (whitespace, pi_value),
		    tail)
	   }

	 | _ ->
	   return (Some (whitespace, pi_value),
		   tail)

	  }

endspec