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
	    hard_error (EOF {context = "parsing PI",
			     start   = start})
    in
      {
       %%
       %%  [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
       %%
       (target, tail_0) <- parse_GenericName start;
       (when (~ (pi_target? target))
	(error (Surprise {context = "Parsing PI",
			  expected = [("Name - 'xml' variants", "legal PI target name")], 
			  action   = "Pretend name is acceptable",
			  start    = start,
			  tail     = tail_0,
			  peek     = 10})));

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
	       (error (Surprise {context = "Parsing PI value",
				 expected = [(" ", "whitespace")],
				 action   = "Pretend whitespace was seen",
				 start    = start,
				 tail     = tail,
				 peek     = 10})));
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