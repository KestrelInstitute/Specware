Rational qualifying spec

  type Rational

  op denominator : Rational -> Rational
  op numerator : Rational -> Rational
  
  op +   infixl 25 : Rational * Rational -> Rational
  op -   infixl 25 : Rational * Rational -> Rational
  op *   infixl 27 : Rational * Rational -> Rational
  op div infixl 26 : Rational * NonNegativeRational -> Rational
  op rem infixl 26 : Rational * NonNegativeRational -> Rational
  op <=  infixl 20 : Rational * Rational -> Boolean
  op <   infixl 20 : Rational * Rational -> Boolean
  op >=  infixl 20 : Rational * Rational -> Boolean
  op >   infixl 20 : Rational * Rational -> Boolean
  op abs           : Rational -> NonNegativeRational
  op min           : Rational * Rational -> Rational
  op max           : Rational * Rational -> Rational
  op compare       : Rational * Rational -> Comparison
  op pred          : Nat -> Rational

  op intToRat: Integer -> Rational
  op ratToInt : Rational -> Integer

  op Rational_.- : Rational -> Rational

  op ratToString : Rational -> String
  op toString : Rational -> String
  def toString(x) = ratToString(x)

%  op stringToRat : (String | Integer.intConvertible) -> Integer

  op zero: Rational
  op one: Rational

  def > (r1,r2) = r2 < r1

  def <= (r1,r2) = r1 < r2 || r1 = r2

  def >= (r1,r2) = r2 >= r1

  % non-negative:

  op nonNegative? : Rational -> Boolean
  def nonNegative? r = r >= zero

  type NonNegativeRational = (Rational | nonNegative?)

  def abs r = if nonNegative? r then r else - r

  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal



endspec
