XML qualifying spec

  import Parse_GenericTag

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          PI                                                                                  %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% *[16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>' 
  %%   ==>
  %% [K10]  PI        ::= '<?' PITarget (S PIValue)? '?>'           
  %% [K11]  PIValue   ::= Char* - (Char* '?>' Char*)
  %%
  %%  [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %% 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %% 
  %% [K10]  PI        ::= '<?' PITarget (S PIValue)? '?>'           
  %% [K11]  PIValue   ::= Char* - (Char* '?>' Char*)
  %%  [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %% 
  %% -------------------------------------------------------------------------------------------------

  def parse_PI (start : UChars) : Required PI =
    %% assumes we're past initial '<?'
    let 
      %%
      %% [K11]  PIValue   ::= Char* - (Char* '?>' Char*)
      %%
      def probe (tail, rev_result) =
	case tail of
	  | 63 :: 62 (* '?>' *) :: tail ->
	    return (rev rev_result,
		    tail)
	  | char :: tail ->
	    probe (tail, cons (char, rev_result))
	  | _ ->
	    error ("EOF scanning PI", start, [])
    in
      {
       %%
       %%  [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
       %%
       (target, tail_0) <- parse_GenericName start;
       (when (~ (pi_target? target))
	(error ("Illegal PI Target name", start, tail_0)));

       (whitespace_and_value, tail) <- probe (tail_0, []);

       %% TODO -- cleaner approach?

       case whitespace_and_value of
	 | char :: tail ->
	   if white_char? char then
	     {
	      (whitespace, value) <- parse_WhiteSpace whitespace_and_value;
	      return ({target = target,
		       value  = Some (whitespace, value)},
		      tail)
	      }
	   else
	     {
	      (when true
	       (error ("PI value must begin with whitespace", whitespace_and_value, [])));
	      return ({target = target,
		       value  = Some ([], whitespace_and_value)},
		      tail)
	     }
	 | _ ->
	     return ({target = target,
		      value  = None},
		     tail_0)
	  }


endspec