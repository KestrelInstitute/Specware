\section{Integer}
\begin{spec}

Integer qualifying spec
  import PrimitiveSorts
  import Compare

  op + infixl 25 : Integer * Integer -> Integer
  op * infixl 27 : Integer * Integer -> Integer
  op - infixl 25 : Integer * Integer -> Integer
  op ~ : Integer -> Integer

  op <  infixl 20 : Integer * Integer -> Boolean
  op <= infixl 20 : Integer * Integer -> Boolean
  op >  infixl 20 : Integer * Integer -> Boolean
  op >= infixl 20 : Integer * Integer -> Boolean
  op min : Integer * Integer -> Integer
  op max : Integer * Integer -> Integer

  %% toString is the same as intToString.
  %% show is the same as intToString.
  %% toString and natToString to be deprecated.

  op toString    : Integer -> String
  op show        : Integer -> String
  op intToString : Integer -> String
  op stringToInt : String -> Integer

  % axiom less-or-equal is fa(x,y) (x <= y)  <=>  ((x < y) or (x = y)  )

  def min (x,y) = if x <= y then x else y
  def max (x,y) = if x <= y then y else x

  def >  (x,y) = y <  x
  def >= (x,y) = y <= x

  op compare : Integer * Integer -> Comparison

  def compare (n,m)  =
    if n < m then
      Less
    else
      if n = m then
        Equal
      else
        Greater        

  def show n = toString n
endspec
\end{spec}
