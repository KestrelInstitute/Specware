Char qualifying spec

  import Integer

  (* We consider the 8-bit characters occupying decimal positions 0 to 255 in
  the ISO-8859-1 code table (the first 128 characters of that code table are
  the ASCII characters). Thus, we define type Char by isomorphism with natural
  numbers less than 256. *)

  type Char.Char  % qualifier required for internal parsing reasons

  % map character to its position in the code table:

  op ord : Char -> {n : Nat | n < 256}

  axiom ord_is_isomorphism is bijective? ord

  % other ops on characters:

  op chr : {n : Nat | n < 256} -> Char
  def chr = inverse ord

  op isUpperCase : Char -> Boolean
  def isUpperCase c = (ord #A <= ord c && ord c <= ord #Z)

  op isLowerCase : Char -> Boolean
  def isLowerCase c = (ord #a <= ord c && ord c <= ord #z)

  op isAlpha : Char -> Boolean
  def isAlpha c = isUpperCase c || isLowerCase c

  op isNum : Char -> Boolean
  def isNum c = (ord #0 <= ord c && ord c <= ord #9)

  op isAlphaNum : Char -> Boolean
  def isAlphaNum c = isAlpha c || isNum c

  op isAscii : Char -> Boolean
  def isAscii c = ord c < 128

  op toUpperCase : Char -> Char
  def toUpperCase c = if isLowerCase c
                      then chr(ord c - ord #a + ord #A)
                      else c

  op toLowerCase : Char -> Char
  def toLowerCase c = if isUpperCase c
                      then chr(ord c - ord #A + ord #a)
                      else c

  op compare : Char * Char -> Comparison
  def compare(c1,c2) = compare(ord c1, ord c2)

endspec
