XML qualifying spec

  import Parse_Literals
  import Parse_Character_Strings

  %% ====================================================================================================
  %%
  %% [23] [40] [44] are instances of [K3]:
  %% 
  %% [K3]  GenericTag         ::= '<' GenericName GenericAttributes WhiteSpace? EndChars? '>'
  %% [K4]  GenericName        ::= ...
  %% [K5]  GenericAttributes  ::= GenericAttribute*
  %% [K6]  GenericAttribute   ::= GenericName Eq GenericValue 
  %% 
  %% [16]  PI        ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>' 
  %% [17]  PITarget  ::=  Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))
  %%
  %% [K7]  PI        ::= '<?' PITarget (S PIValue)? '?>'           
  %% [K8]  PIValue   ::= Char* - (Char* '?>' Char*)
  %% 
  %% ====================================================================================================

  def parse_Option_GenericTag (start : UChars) : Possible GenericTag =
    case start of
      | 60 (* < *) :: tail -> 
         {
	  (prefix,     tail) <- parse_GenericPrefix      tail;
	  (name,       tail) <- parse_GenericName        tail;
	  (attributes, tail) <- parse_GenericAttributes  tail;
	  (whitespace, tail) <- parse_WhiteSpace         tail;
	  (postfix,    tail) <- parse_GenericPostfix     tail;
	  return (Some {prefix     = prefix,
			name       = name,
			attributes = attributes,
			whitespace = whitespace,
			postfix    = postfix},
		  tail)
	  }
      | _ ->
	 return (None, start)

  def parse_GenericPrefix (start : UChars) : Required UString =
    %%
    %% This should typically proceed for only a few characters.
    %% It's expecting '' '?' '/'  etc.
    %% but might get nonsense, which will be detected later.
    %% At any rate, don't go more than about 5 characters before 
    %% complaining.
    %%
    %% Return the chars up to, but not including, the close angle,
    %% plus the tail just past that close angle.
    %%
    let
       def probe (tail, n, rev_end_chars) =
	 if n < 1 then
	   error ("Expected namechar soon after <", start, tail)
	 else
	   case tail of
	     | char :: scout ->
	       if name_char? char then
		 return (rev rev_end_chars,
			 tail)
	       else
		 probe (scout, n - 1, cons (char, rev_end_chars))
	     | _ ->
		 error ("EOF looking for namechar after '<'", start, tail)
    in
      probe (start, 5, [])

  def parse_GenericName (start : UChars) : Required UString =
    parse_NmToken start

  def parse_GenericAttributes (start : UChars) : Required GenericAttributes =
    let 
       def probe (tail, rev_attrs) =
	 {
	  (possible_attribute, scout) <- parse_GenericAttribute tail;
	  case possible_attribute of
	    | None -> 
	      return (rev rev_attrs, 
		      tail)
	    | Some attr ->
	      probe (scout, cons (attr, rev_attrs))
	     }
    in
      probe (start, [])

  def parse_GenericAttribute (start : UChars) : Possible GenericAttribute =
    {
     (w1,    tail) <- parse_WhiteSpace start;
     case tail of
       | char :: _ ->
	 if name_char? char then
	   {
	    (name,   tail) <- parse_NmToken    tail;
	    (w2,     tail) <- parse_WhiteSpace tail;
	    (eqchar, tail) <- parse_EqualSign  tail;
	    (w3,     tail) <- parse_WhiteSpace tail;
	    (value,  tail) <- parse_QuotedText tail;
	    return (Some {w1     = w1,
			  name    = name,
			  w2      = w2,
			  %% =
			  w3      = w3,
			  value   = value},
		    tail)
	   }
	 else
	   return (None, start)
       | _ ->
	   return (None, start)
	  }	   

  def parse_GenericPostfix (start : UChars) : Required UString =
    %%
    %% This should typically proceed for only about 0 or 1 characters.
    %% It's expecting '>' '?>' '/>' ']]>' etc.
    %% but might get nonsense, which will be detected later.
    %% At any rate, don't go more than about 5 characters before 
    %% complaining.
    %%
    %% Return the chars up to, but not including, the close angle,
    %% plus the tail just past that close angle.
    %%
    let
       def probe (tail, n, rev_end_chars) =
	 if n < 1 then
	   error ("Expected '>'", start, tail)
	 else
	   case tail of
	     | char :: tail ->
	       if char = 62 (* > *) then
		 return (rev rev_end_chars,
			 tail)
	       else
		 probe (tail, n - 1, cons (char, rev_end_chars))
	     | _ ->
	       error ("EOF looking for '>'", start, tail)
    in
      probe (start, 5, [])

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
       (target, tail_0) <- parse_GenericName start;

       (when (~ (pi_target? target))
	(error ("Illegal PI Target name", start, tail_0)));

       (whitespace_and_value, tail) <- probe (tail_0, []);

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


