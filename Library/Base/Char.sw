\section{Char}

\begin{spec}
Char qualifying spec
  import PrimitiveSorts
  import Nat
  import Compare

  op toString : Char -> String
  op show : Char -> String
  def show c = toString c

  op isUpperCase : Char -> Boolean
  op isLowerCase : Char -> Boolean
  op isAlphaNum  : Char -> Boolean
  op isAlpha     : Char -> Boolean
  op isNum       : Char -> Boolean
  op isAscii     : Char -> Boolean
  op toUpperCase : Char -> Char 
  op toLowerCase : Char -> Char
  op ord         : Char -> Nat

  op chr         : Nat  -> Char

  op compare     : Char * Char -> Comparison
endspec
\end{spec}
