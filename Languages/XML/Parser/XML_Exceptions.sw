XML qualifying spec

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

  sort XML_Exception =
    | EOF         EOF_Error
    | Surprise    Surprise_Error
    | WFC         WFC_Error        % well-formedness condition
    | VC          VC_Error         % validity condition
    | KC          KC_Error         % kestrel well-formedness condition

  def print_pending_XML_Exceptions (state : State) : String =
    %% maybe be sensitive to context ?
    case state.exceptions of
      | [] -> ""
      | exceptions ->
        "\nXML Errors:\n " ^
	(foldl (fn (exception, result) -> result ^ (print_one_XML_Exception (exception, state.utext))) "" exceptions) ^
	"\n"

  def print_one_XML_Exception (exception : XML_Exception, utext : UChars) : String =
    "\n" ^
    (case exception of
       | EOF      x -> print_EOF_Error      (x, utext)
       | Surprise x -> print_Surprise_Error (x, utext)
       | WFC      x -> print_WFC_Error      x
       | VC       x -> print_VC_Error       x
       | KC       x -> print_KC_Error       x
       ) ^ "\n"
       
  %% --------------------------------------------------------------------------------

  sort EOF_Error = {context : String,
		    start   : UChars}

  def print_EOF_Error (x : EOF_Error, utext : UChars) : String =
    let (line, column, byte) = location_of (x.start, utext) in
    let location = (Nat.toString line) ^ ":" ^ (Nat.toString column) ^ " (byte " ^ (Nat.toString byte) ^ ")" in
    "EOF error " ^ x.context ^ ", starting at " ^ location

  %% --------------------------------------------------------------------------------

  sort Surprise_Error = {context  : String,
			 action   : String,
			 expected : List (String * String),
			 start    : UChars,
			 tail     : UChars,
			 peek     : Nat}

  def print_Surprise_Error (surprise, utext) : String =
    let max_length = foldl (fn ((s1, _), max_length) -> max (max_length, length s1)) 0 surprise.expected in
    let (line, column, byte) = location_of (surprise.start, utext) in
    let location = (Nat.toString line) ^ ":" ^ (Nat.toString column) ^ " (byte " ^ (Nat.toString byte) ^ ")" in
    let 
       def pad n =
	 if n >= max_length then
	   ""
	 else
	   " " ^ pad (n + 1)
    in
      "\n "                ^ surprise.context 
    ^ "\n at "             ^ location 
    ^ "\n having viewed [" ^ (string (prefix_to_tail (surprise.start, surprise.tail))) ^ "]"
    ^ "\n  with pending [" ^ (string (prefix_for_n   (surprise.tail,  surprise.peek))) ^ "]"
    ^ "\n expected one of: " 
    ^ (foldl (fn ((s1, s2), result) -> 
		result ^ "\n    " ^ s1 ^ (pad (length s1)) ^ " for " ^ s2) 
	       "" 
	       surprise.expected) 
      ^ "\n so took action: " ^ surprise.action

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

  %% --------------------------------------------------------------------------------

  sort WFC_Error  = {description : String}
  def print_WFC_Error x : String =
       "WFC (Well-Formedness Condition): " ^ x.description

  sort VC_Error   = {description : String}
  def print_VC_Error x : String =
       "VC (Validity Condition): " ^ x.description

  sort KC_Error   = {description : String}
  def print_KC_Error x : String =
       "KC (Kestrel-specific well-formedness condition): " ^ x.description

  %% --------------------------------------------------------------------------------

endspec