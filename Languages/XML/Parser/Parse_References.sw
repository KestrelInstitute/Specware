
XML qualifying spec

  import Parse_Names

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%          References                                                                          %%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%
  %% [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';' 
  %%
  %%                                                             [WFC: Legal Character]
  %%
  %% [67]  Reference    ::=  EntityRef | CharRef
  %%
  %% [68]  EntityRef    ::=  '&' Name ';' 
  %%
  %%                                                             [WFC: Entity Declared]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: Parsed Entity] 
  %%                                                             [WFC: No Recursion]
  %%
  %% [69]  PEReference  ::=  '%' Name ';' 
  %%
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: No Recursion]
  %%                                                             [WFC: In DTD]
  %%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% -------------------------------------------------------------------------------------------------
  %%
  %% [67]  Reference    ::=  EntityRef | CharRef
  %% [68]  EntityRef    ::=  '&' Name ';' 
  %%
  %%                                                             [WFC: Entity Declared]
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: Parsed Entity] 
  %%                                                             [WFC: No Recursion]
  %%
  %% [66]  CharRef      ::=  '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';' 
  %%
  %%                                                             [WFC: Legal Character]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_Reference (start : UChars) : Required Reference =
    %%  We being just past the '&' in rules [66] and [68], looking for one of:
    %%
    %%     '#x' [0-9a-fA-F]+ ';' 
    %%     '#'  [0-9]+       ';' 
    %%     Name              ';' 
    %%
    case start of
      | 35 (* '#' *) :: tail ->
        %% parse CharRef
        (case tail of
	   | 120 (* 'x' *) :: tail ->
             %% hex ...
             (case parse_hex tail of
		| Some (char, tail) ->
		  (case tail of
		     | 59  (* ';' *) :: tail ->
		       {
		        (when (~ (char? char))
			 (error (Surprise {context  = "Illegal (hex) character reference",
					   action   = "Passing bogus character along",
					   expected = [("hex digits", "legal Unicode character")],
					   start    = start,
					   tail     = tail,
					   peek     = 0})));
		        return (Char {style = Hex,
				      char  = char},
				tail)
			}
		     | _ -> 
		       {error (Surprise {context  = "Illegal (hex) character reference ",
					 action   = "Pretending ';' was seen",
					 expected = [(";", "termination of hex character reference")],
					 start    = start,
					 tail     = tail,
					 peek     = 10});
		        return (Char {style = Hex,
				      char  = char},
				tail)
			})
		| _ -> 
		     hard_error (Surprise {context  = "Illegal (hex) character reference ",
					   action   = "Immediate failure",
					   expected = [("[0-9A-Fa-f", "hex digit")],
					   start    = start,
					   tail     = tail,
					   peek     = 10}))
	   | _ ->
	     case parse_decimal tail of
	       | Some (char, tail) ->
		 (case tail of
		    | 59  (* ';' *) :: tail ->
		      {
		       (when (~ (char? char))
			 (error (Surprise {context  = "Illegal (decimal) character reference ",
					   action   = "Passing bogus character along",
					   expected = [("decimal digits", "legal Unicode character")],
					   start    = start,
					   tail     = tail,
					   peek     = 0})));
		       return (Char {style = Decimal,
				     char  = char},
			       tail)
		       }
		    | _ -> 
		      {
		       error (Surprise {context  = "Illegal (decimal) character reference ",
					action   = "Pretending ';' was seen",
					expected = [(";", "termination of decimal character reference")],
					start    = start,
					tail     = tail,
					peek     = 10});
		       return (Char {style = Decimal,
				     char  = char},
			       tail)
		       })
	       | _ -> 
		    hard_error (Surprise {context  = "Illegal (decimal) character reference ",
					  action   = "Immediate failure",
					  expected = [("[0-9", "decimal digit")],
					  start    = start,
					  tail     = tail,
					  peek     = 10}))
      | _ ->
	%% parse EntityRef
	{
	 (name, tail) <- parse_Name start;
	 case tail of
	   | 59  (* ';' *) :: tail ->
	     return (Entity {name = name},
		     tail)
	   | _ -> 
	     {error (Surprise {context  = "Illegal entity reference",
			       action   = "Pretending ';' was seen",
			       expected = [(";", "termination of entity reference")],
			       start    = start,
			       tail     = tail,
			       peek     = 10});
	      return (Entity {name = name},
		      tail)
	     }}



  %% -------------------------------------------------------------------------------------------------
  %%
  %% [69]  PEReference  ::=  '%' Name ';' 
  %%
  %%                                                             [VC:  Entity Declared]
  %%                                                             [WFC: No Recursion]
  %%                                                             [WFC: In DTD]
  %%
  %% -------------------------------------------------------------------------------------------------

  def parse_PEReference (start : UChars) : Required PEReference =
    {
     %% We begin just past the '%", looking for:
     %%			 
     %%   Name ';' 
     %%			 
     (name, tail) <- parse_Name start;
     case tail of
       | 59  (* ';' *) :: tail ->
         return ({name = name},
		 tail)
       | _ -> 
	 {error (Surprise {context  = "Expecting PEReference",
			   action   = "Pretending ';' was seen",
			   expected = [(";", "termination of PE Reference")],
			   start    = start,
			   tail     = tail,
			   peek     = 10});
	  return ({name = name},
		  tail)
	 }}

  %% -------------------------------------------------------------------------------------------------

  def parse_decimal (start : UChars) : Option (Nat * UChars) =
   let 
      def probe (tail, n) =
	case tail of
	  |  48 (* '0' *) :: tail -> probe (tail, 10 * n)
	  |  49 (* '1' *) :: tail -> probe (tail, 10 * n + 1)
	  |  50 (* '2' *) :: tail -> probe (tail, 10 * n + 2)
	  |  51 (* '3' *) :: tail -> probe (tail, 10 * n + 3)
	  |  52 (* '4' *) :: tail -> probe (tail, 10 * n + 4)
	  |  53 (* '5' *) :: tail -> probe (tail, 10 * n + 5)
	  |  54 (* '6' *) :: tail -> probe (tail, 10 * n + 6)
	  |  55 (* '7' *) :: tail -> probe (tail, 10 * n + 7)
	  |  56 (* '8' *) :: tail -> probe (tail, 10 * n + 8)
	  |  57 (* '9' *) :: tail -> probe (tail, 10 * n + 9)
	  | _ ->
	    if start = tail then
	      Some (n, tail)
	    else
	      None
   in
     probe (start, 0)

  %% -------------------------------------------------------------------------------------------------

  def parse_hex (start : UChars) : Option (Nat * UChars) =
   let 
      def probe (tail, n) =
	case tail of
	  |  48 (* '0' *) :: tail -> probe (tail, 10 * n)
	  |  49 (* '1' *) :: tail -> probe (tail, 10 * n + 1)
	  |  50 (* '2' *) :: tail -> probe (tail, 10 * n + 2)
	  |  51 (* '3' *) :: tail -> probe (tail, 10 * n + 3)
	  |  52 (* '4' *) :: tail -> probe (tail, 10 * n + 4)
	  |  53 (* '5' *) :: tail -> probe (tail, 10 * n + 5)
	  |  54 (* '6' *) :: tail -> probe (tail, 10 * n + 6)
	  |  55 (* '7' *) :: tail -> probe (tail, 10 * n + 7)
	  |  56 (* '8' *) :: tail -> probe (tail, 10 * n + 8)
	  |  57 (* '9' *) :: tail -> probe (tail, 10 * n + 9)

	  |  65 (* 'A' *) :: tail -> probe (tail, 10 * n + 10)
	  |  66 (* 'B' *) :: tail -> probe (tail, 10 * n + 11)
	  |  67 (* 'C' *) :: tail -> probe (tail, 10 * n + 12)
	  |  68 (* 'D' *) :: tail -> probe (tail, 10 * n + 13)
	  |  69 (* 'E' *) :: tail -> probe (tail, 10 * n + 14)
	  |  70 (* 'F' *) :: tail -> probe (tail, 10 * n + 15)
	  
	  |  97 (* 'a' *) :: tail -> probe (tail, 10 * n + 10)
	  |  98 (* 'b' *) :: tail -> probe (tail, 10 * n + 11)
	  |  99 (* 'c' *) :: tail -> probe (tail, 10 * n + 12)
	  | 100 (* 'd' *) :: tail -> probe (tail, 10 * n + 13)
	  | 101 (* 'e' *) :: tail -> probe (tail, 10 * n + 14)
	  | 102 (* 'f' *) :: tail -> probe (tail, 10 * n + 15)
	  | _ ->
	    if start = tail then
	      Some (n, tail)
	    else
	      None
   in
     probe (start, 0)


endspec
