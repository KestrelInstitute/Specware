
XML qualifying spec

  import Parse_Names
  import Parse_GenericTag

  %% ----------------------------------------------------------------------------------------------------
  %%  [3]  S  ::=  (#x20 | #x9 | #xD | #xA)+
  %% ----------------------------------------------------------------------------------------------------



  %% ----------------------------------------------------------------------------------------------------
  %% [15]  Comment  ::=  '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
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
  %%
  %% [K7]  PI                ::= '<?' PITarget NoQMarkCloseAngle '?>'           
  %% [K8]  NoQMarkCloseAngle ::= Char* - (Char* '?>' Char*)
  %%
  %% [16]  PI                ::= '<?' PITarget (S (Char* - (Char* '?>' Char* )))? '?>' 
  %%                         === [K7] assuming first char, if any, in NoQMarkCloseAngle is whitespace
  %% ----------------------------------------------------------------------------------------------------

  def parse_PI (start : UChars) : Required PI =
    %% assumes we're past initial '<?'
    let 
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
       (target,       tail_0) <- parse_GenericName start;
       (instructions, tail)   <- probe (tail_0, []);

       (when (~ (pi_target? target))
	(error ("Illegal PI Target name", start, tail_0)));

       (when (~ (white_char? (hd instructions)))
	(error ("PI Instructions must begin with whitespace", tail_0, tail)));

       return ({target = target,
		text   = instructions},
	       tail)
      }



endspec