XML qualifying spec

  import ../Utilities/XML_Base
  import ../Utilities/XML_Unicode

  sort State = {exceptions : List XML_Exception, % for deferred processing
		messages   : List String,
		utext      : UString,
		context    : Processing_Environment}

  def initialState (uchars : UChars) : State =
    {exceptions = [], 
     messages   = [], 
     utext      = uchars,
     context    = default_processing_environment}

  sort Processing_Environment = {tracing? : Boolean} % could add verbosity, etc.

  def default_processing_environment : Processing_Environment = 
    {tracing? = Trace_XML_Parser?}

  def Trace_XML_Parser? : Boolean = false

  sort XML_Exception = {kind        : XML_Exception_Type,
			requirement : String,
			problem     : String,
			expected    : List (String * String),
			start       : UChars,
			tail        : UChars,
			peek        : Nat,
			action      : String}
			

  sort XML_Exception_Type = | EOF         
                            | Syntax
                            | WFC         
                            | VC          
                            | KC          

  def print_pending_XML_Exceptions (state : State) : String =
    %% maybe be sensitive to context ?
    case state.exceptions of
      | [] -> ""
      | exceptions ->
        "\nXML Errors:\n" ^
	(foldl (fn (exception, result) -> result ^ (print_one_XML_Exception (exception, state.utext))) "" (rev exceptions)) ^
	"\n\n"

  def print_one_XML_Exception (x : XML_Exception, utext : UChars) : String =
    
    let (line, column, byte) = location_of (x.start, utext) in
    let location = (Nat.toString line) ^ ":" ^ (Nat.toString column) ^ " (byte " ^ (Nat.toString byte) ^ ")" in

      "\n At "       ^ location 

    ^ "\n " ^ ((case x.kind of
		  | EOF       -> "EOF"
		  | Syntax    -> "Syntax"
		  | WFC       -> "WFC (Well-Formedness Condition)"
		  | VC        -> "VC  (Validity Condition)"
		  | KC        -> "KC  (Kestrel-specific well-formedness condition)")
	       ^ " error: ")
    ^ "\n "     ^ x.requirement
    ^ "\n but " ^ x.problem 
    ^ "\n while viewing [" ^ (string (prefix_to_tail (x.start, x.tail))) ^ "]"
    ^ " with pending [" ^ (string (prefix_for_n   (x.tail,  x.peek))) ^ "]"
    ^ (case x.expected of
	 | []  -> "\n <no expectations?> \n"
	 | [_] -> "\n expected: \n"
	 | _   -> "\n expected one of: \n") 
    ^ (let max_length = foldl (fn ((s1, _), max_length) -> max (max_length, length s1)) 0 x.expected in
       let 
         def pad n =
	   if n >= max_length then
	     ""
	   else
	     " " ^ pad (n + 1)
       in
	 foldl (fn ((s1, s2), result) -> 
		result ^ "\n    " ^ s1 ^ (pad (length s1)) ^ " -- " ^ s2) 
	       "" 
	       x.expected)
    ^ "\n\n so taking action: " ^ x.action
    ^ "\n"       

  %% --------------------------------------------------------------------------------


  def location_of (target : UChars, utext : UChars) : Nat * Nat * Nat =
    let
      def aux (tail, line, column, byte) =
	if tail = target then
	  (line, column, byte)
	else
	  case tail of
	    | [] -> (line, column, byte)
	    | char :: tail -> 
	      case char of
		| 10 -> aux (tail, line + 1, 0,          byte + 1)
		| _  -> aux (tail, line,     column + 1, byte + 1)
    in
      aux (utext, 0, 0, 0)

  def prefix_to_tail (start : UChars, tail : UChars) : UChars =
    let
      def aux (start, rev_chars) =
	if start = tail then
	  rev rev_chars
	else
	  case start of
	    | [] -> rev rev_chars
	    | x :: y -> aux (y, cons (x, rev_chars))
    in
      aux (start, [])

  def prefix_for_n (start : UChars, n : Nat) : UChars =
    let
      def aux (tail, i, rev_chars) =
	if i >= n then
	  rev rev_chars
	else
	  case tail of
	    | [] -> rev rev_chars
	    | x :: tail -> aux (tail, i + 1, cons (x, rev_chars))
    in
      aux (start, 0, [])

  def describe_char char =
    "'" ^ (string [char]) ^ "' (#x" ^ (toHex char) ^ "; = #" ^ (Nat.toString char) ^ ";)"

endspec