Char qualifying spec

  % refinement of base spec Nat

  import Nat

  % sorts:

  % sort Char

  % ops whose Lisp code is hand-written:

 %op ord : Char -> {n : Nat | n < 256}
  op chr : {n : Nat | n < 256} -> Char
  op isUpperCase : Char -> Boolean
  op isLowerCase : Char -> Boolean
  op isAlpha     : Char -> Boolean
  op isNum       : Char -> Boolean
  op isAlphaNum  : Char -> Boolean
  op isAscii     : Char -> Boolean
  op toUpperCase : Char -> Char
  op toLowerCase : Char -> Char

  % axioms copied from base spec Char:

  axiom chr_def is
    fa (n : Nat) n < 256 => ord(chr n) = n

  axiom isUpperCase_def is
    fa (c : Char) isUpperCase c <=> (ord #A <= ord c & ord c <= ord #Z)

  axiom isLowerCase_def is
    fa (c : Char) isLowerCase c <=> (ord #a <= ord c & ord c <= ord #z)

  axiom isAlpha_def is
    fa (c : Char) isAlpha c <=> isUpperCase c or isLowerCase c

  axiom isNum_def is
    fa (c : Char) isNum c <=> (ord #0 <= ord c & ord c <= ord #9)

  axiom isAlphaNum_def is
    fa (c : Char) isAlphaNum c <=> isAlpha c or isNum c

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

  % ops whose Lisp code is generated:

  op compare : Char * Char -> Comparison

  def compare(c1,c2) = compare(ord c1, ord c2)

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op toString : Char -> String  % deprecated
  % op show     : Char -> String

endspec
