(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import ../Utilities/XML_Base
  import ../Utilities/XML_Unicode
  import EntityMaps

  type State = {exceptions : List XML_Exception, % for deferred processing
		messages   : List String,
		utext      : UString,
		ge_defs    : GE_Map,
		pe_defs    : PE_Map,
		context    : Processing_Environment}

  def initialState (uchars : UChars) : State =
    {exceptions = [],
     messages   = [],
     utext      = uchars,
     ge_defs    = empty_map,
     pe_defs    = empty_map,
     context    = default_processing_environment}

  type Processing_Environment = {tracing? : Bool} % could add verbosity, etc.

  def default_processing_environment : Processing_Environment =
    {tracing? = Trace_XML_Parser?}

  def Trace_XML_Parser? : Bool = false

  type XML_Exception = {kind        : XML_Exception_Type,
			requirement : String,
			start       : UChars,
			tail        : UChars,
			peek        : Nat,
			we_expected : List (String * String),
			but         : String,
			so_we       : String}

  type XML_Exception_Type = | EOF
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
	(foldl (fn (result, exception) -> result ^ (print_one_XML_Exception (exception, state.utext)))
	  "" (reverse exceptions)) ^
	"\n\n"

  def print_one_XML_Exception (x : XML_Exception, utext : UChars) : String =
    let (line, column, byte) = location_of (x.start, utext) in
    let location = (Nat.show line) ^ ":" ^ (Nat.show column) ^ " (byte " ^ (Nat.show byte) ^ ")" in

      "\n At " ^ location
    ^ "\n " ^ (case x.kind of
		 | EOF       -> "EOF: "
		 | Syntax    -> "Syntax error: "
		 | WFC       -> "WFC (Well-Formedness Condition): "
		 | VC        -> "VC  (Validity Condition): "
		 | KC        -> "KC  (Kestrel-specific well-formedness condition): ")
    ^ x.requirement
    ^ "\n Viewing ["    ^ (string (prefix_to_tail (x.start, x.tail))) ^ "]"
    ^ " with pending [" ^ (string (prefix_for_n   (x.tail,  x.peek))) ^ "],"
    ^ (case x.we_expected of
	 | []  -> "\n <we had no expectations?> \n"
	 | [_] -> "\n we expected: \n"
	 | _   -> "\n we expected one of: \n")
    ^ (let max_length = foldl (fn (max_length, (s1, _)) -> max (max_length, length s1)) 0 x.we_expected in
       let
         def pad n =
	   if n >= max_length then
	     ""
	   else
	     " " ^ pad (n + 1)
       in
	 foldl (fn (result, (s1, s2)) ->
		result ^ "\n    " ^ s1 ^ (pad (length s1)) ^ " -- " ^ s2)
	       ""
	       x.we_expected)
    ^ "\n\n but " ^ x.but ^ ","
    ^ "\n so we " ^ x.so_we
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
	  reverse rev_chars
	else
	  case start of
	    | [] -> reverse rev_chars
	    | x :: y -> aux (y,  x::rev_chars)
    in
      aux (start, [])

  def prefix_for_n (start : UChars, n : Nat) : UChars =
    let
      def aux (tail, i, rev_chars) =
	if i >= n then
	  reverse rev_chars
	else
	  case tail of
	    | [] -> reverse rev_chars
	    | x :: tail -> aux (tail, i + 1,  x::rev_chars)
    in
      aux (start, 0, [])

  def describe_char char =
    "'" ^ (string [char]) ^ "' (= #x" ^ (toHex char) ^ "; = #" ^ (Nat.show char) ^ ";)"

endspec
