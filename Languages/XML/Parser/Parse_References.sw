
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
  %% ----------------------------------------------------------------------------------------------------

  def parse_Reference (start : UChars) : Possible Reference =
    %% parse_Reference assumes we're just past the ampersand.
    case start of
      | 35 (* '#' *) :: tail ->
        (case tail of
	   | 120 (* 'x' *) :: tail ->
             %% hex ...
             (case parse_hex tail of
		| Some (char, tail) ->
		  (case tail of
		     | 59  (* ';' *) :: tail ->
		       {
		        (when (~ (char? char))
			 (error ("Illegal character reference ", start, tail)));
		        return (Some (Char {style = Hex,
					    char  = char}),
				tail)
			}
		     | _ -> return (None, start))
		| _ -> return (None, start)) % no hex digits

           | _ ->
	     case parse_decimal tail of
	       | Some (char, tail) ->
		 (case tail of
		    | 59  (* ';' *) :: tail ->
		      {
		       (when (~ (char? char))
			(error ("Illegal character reference ", start, tail)));
		       return (Some (Char {style = Decimal,
					   char  = char}),
			       tail)
		       }
		    | _ -> return (None, start))
	       | _ -> return (None, start))
      | _ ->
	{
	 (name, tail) <- parse_Name start;
	 case tail of
	   | 59  (* ';' *) :: tail ->
	     return (Some (Entity {name = name}),
		     tail)
	   | _ -> return (None, start)
	}

    
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
