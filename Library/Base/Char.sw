Char qualifying spec

  import Integer

  (* We consider the 8-bit characters occupying decimal positions 0 to 255 in
  the ISO-8859-1 code table (the first 128 characters of that code table are
  the ASCII characters). Thus, we define type Char by isomorphism with natural
  numbers less than 256. *)

  type Char.Char  % qualifier required for internal parsing reasons

  % maps character to its position in the code table:
  op ord : Char -> {n : Nat | n < 256}

  axiom ord_is_isomorphism is
    bijective? ord

  % other ops on characters:

  op chr         : {n : Nat | n < 256} -> Char
  op isUpperCase : Char -> Boolean
  op isLowerCase : Char -> Boolean
  op isAlpha     : Char -> Boolean
  op isNum       : Char -> Boolean
  op isAlphaNum  : Char -> Boolean
  op isAscii     : Char -> Boolean
  op toUpperCase : Char -> Char
  op toLowerCase : Char -> Char
  op compare     : Char * Char -> Comparison

  axiom chr_def is
    chr = inverse ord

  axiom isUpperCase_def is
    fa (c : Char) isUpperCase c <=> (ord #A <= ord c && ord c <= ord #Z)

  axiom isLowerCase_def is
    fa (c : Char) isLowerCase c <=> (ord #a <= ord c && ord c <= ord #z)

  axiom isAlpha_def is
    fa (c : Char) isAlpha c <=> isUpperCase c || isLowerCase c

  axiom isNum_def is
    fa (c : Char) isNum c <=> (ord #0 <= ord c && ord c <= ord #9)

  axiom isAlphaNum_def is
    fa (c : Char) isAlphaNum c <=> isAlpha c || isNum c

  axiom isAscii_def is
    fa (c : Char) isAscii c <=> ord c < 128

  axiom toUpperCase_def is
    fa (c : Char) toUpperCase c = (if isLowerCase c
                                   then chr(ord c - ord #a + ord #A)
                                   else c)

  axiom toLowerCase_def is
    fa (c : Char) toLowerCase c  = (if isUpperCase c
                                    then chr(ord c - ord #A + ord #a)
                                    else c)

  def compare(c1,c2) = compare(ord c1, ord c2)

endspec
