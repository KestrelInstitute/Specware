
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
	     {
	      (char, tail) <- parse_hex tail;
	      (when (~ (char? char))
	       (error {kind        = Syntax,
		       requirement = "Not all numbers are legal Unicode characters.",
		       start       = start,
		       tail        = tail,
		       peek        = 0,
		       we_expected = [("<see doc>", "hex code for legal Unicode character")],
		       but         = (describe_char char) ^ "is not a legal Unicode character",
		       so_we       = "pass along the bogus character"}));
	      case tail of
		| 59  (* ';' *) :: tail ->
		  return (Char {style = Hex,
				char  = char},
			  tail)
		| char :: _ ->
		  {
		   error {kind        = Syntax,
			  requirement = "Hex character references must terminate with ';'.",
			  start       = start,
			  tail        = tail,
			  peek        = 10,
			  we_expected = [("';'", "termination of hex character reference")],
			  but         = (describe_char char) ^ " occurred first",
			  so_we       = "pretend interpolated ';' was seen."};
		   return (Char {style = Hex,
				 char  = char},
			   tail)
		  }
		    
		| _ -> 
		  {
		   error {kind        = EOF,
			  requirement = "Hex character references must terminate with ';'.",
			  start       = start,
			  tail        = tail,
			  peek        = 10,
			  we_expected = [("';'", "termination of hex character reference")],
			  but         = "EOF occurred first",
			  so_we       = "pretend interpolated ';' was seen"};
		   return (Char {style = Hex,
				 char  = char},
			   tail)
		  }}
	   | _ ->
	     {
	      (char, tail) <- parse_decimal tail;
	      (when (~ (char? char))
	       (error {kind        = Syntax,
		       requirement = "Not all numbers are legal Unicode characters.",
		       start       = start,
		       tail        = tail,
		       peek        = 0,
		       we_expected = [("<see doc>", "decimal code for legal Unicode character")],
		       but         = (describe_char char) ^ " is not a legal Unicode character",
		       so_we       = "pretend the bogus character is legal"}));
	      case tail of
		| 59  (* ';' *) :: tail ->
		  return (Char {style = Decimal,
				char  = char},
			  tail)
		| char :: _ -> 
		  {
		   error {kind        = Syntax,
			  requirement = "Character references must terminate with ';'.",
			  start       = start,
			  tail        = tail,
			  peek        = 10,
			  we_expected = [("';'", "termination of decimal character reference")],
			  but         = (describe_char char) ^ " occurred first",
			  so_we       = "pretend interpolated ';' was seen"};
		   return (Char {style = Hex,
				 char  = char},
			   tail)
		  }
		| _ ->
		  {
		   error {kind        = EOF,
			  requirement = "Hex character references must terminate with ';'.",
			  start       = start,
			  tail        = tail,
			  peek        = 10,
			  we_expected = [("';'", "termination of decimal character reference")],
			  but         = "EOF occurred first",
			  so_we       = "pretend interpolated ';' was seen"};
		   return (Char {style = Hex,
				 char  = char},
			   tail)
		  }})
      | _ ->
	%% parse EntityRef
	{
	 (name, tail) <- parse_Name start;
	 case tail of
	   | 59  (* ';' *) :: tail ->
	     return (Entity {name = name},
		     tail)
	   | char :: _ -> 
	     {
	      error {kind        = Syntax,
		     requirement = "Entity references must terminate with ';'.",
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     we_expected = [("';'", "termination of entity reference")],
		     but         = (describe_char char) ^ " occurred first",
		     so_we       = "pretend interpolated ';' was seen"};
	      return (Entity {name = name},
		      tail)
	     }
	   | _ -> 
	     {
	      error {kind        = EOF,
		     requirement = "Entity references must terminate with ';'.",
		     start       = start,
		     tail        = tail,
		     peek        = 10,
		     we_expected = [("';'", "termination of entity reference")],
		     but         = "EOF occurred first",
		     so_we       = "pretend interpolated ';' was seen"};
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
       | char :: _ -> 
	 {
	  error {kind        = Syntax,
		 requirement = "PEReferences must with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of PEReference")],
		 but         = (describe_char char) ^ " occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return ({name = name},
		  tail)
	 }
       | _ -> 
	 {
	  error {kind        = Syntax,
		 requirement = "PEReferences must with ';'.",
		 start       = start,
		 tail        = tail,
		 peek        = 10,
		 we_expected = [("';'", "termination of PEReference")],
		 but         = "EOF occurred first",
		 so_we       = "pretend interpolated ';' was seen"};
	  return ({name = name},
		  tail)
	 }}

  %% -------------------------------------------------------------------------------------------------

  def parse_decimal (start : UChars) : Required UChar =
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
	      {
	       error {kind        = Syntax,
		      requirement = "A decimal number is required.",
		      start       = start,
		      tail        = tail,
		      peek        = 10,
		      we_expected = [("[0-9]+", "decimal digits")],
		      but         = "no decimal digits were seen",
		      so_we       = "pretend '88' (the decimal encoding of 'X') was seen"};
	       return (88, tail)
	       }
	    else
	       return (n, tail)
   in
     probe (start, 0)

  %% -------------------------------------------------------------------------------------------------

  def parse_hex (start : UChars) : Required UChar =
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
	      {
	       error {kind        = Syntax,
		      requirement = "A hex number is required.",
		      start       = start,
		      tail        = tail,
		      peek        = 10,
		      we_expected = [("[0-9A-Fa-f]+", "hex digits")],
		      but         = "no hex digits were seen",
		      so_we       = "pretend '58' (the hex encoding of 'X') was seen"};
	       return (88, tail) (* = hex 58 *)
	      }
	    else
	       return (n, tail)
   in
     probe (start, 0)


endspec
