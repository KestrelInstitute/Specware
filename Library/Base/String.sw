\section{String}

\begin{spec}
String qualifying spec {
  import PrimitiveSorts
  import Nat
  import Boolean
  import Compare
  import List

  op concat : String * String -> String
  op ++ infixl 11 : String * String -> String
  op ^ infixl 11 : String * String -> String
  op length : String -> Nat

  % def ++(s1,s2) = concat(s1,s2)
  % def ^(s1,s2)  = concat(s1,s2)

  op toScreen : String -> ()
  op writeLine : String -> ()
  op newline : String

  op map : (Char -> Char) -> String -> String
  op all : (Char -> Boolean) -> String -> Boolean
  op sub : {(s,n) : String * Nat | (0 <= n) & (n < length(s))} -> Char

  %% Takes start and end; returns s[start...end-1].
  op substring : String * Nat * Nat -> String

  op explode : String -> List Char
  op implode : List Char -> String

  op translate : (Char -> String) -> String -> String

  op leq infixl 20 : String * String -> Boolean % Overload this to <=
  op lt  infixl 20 : String * String -> Boolean % Overload this to <

  op compare : String * String -> Comparison

  def compare (n,m) =
    if n lt m then Less else if n = m then Equal else Greater        

 op concatList : List String -> String
}
\end{spec}

