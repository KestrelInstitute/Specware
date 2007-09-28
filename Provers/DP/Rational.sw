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
  op floor         : Rational -> Integer
  op ceiling       : Rational -> Integer

  op intToRat: Integer -> Rational
  op ratToInt : Rational -> Integer

  op RationalAux.- : Rational -> Rational

  op equal: Rational * Rational -> Boolean
  def equal(r1, r2) = (r1 = r2)

  op ratToString : Rational -> String
  op toString : Rational -> String
  def toString(x) = ratToString(x)

%  op stringToRat : (String | Integer.intConvertible) -> Integer

  op zero: Rational
  op one: Rational

  def > (r1,r2) = r2 < r1

  def <= (r1,r2) = r1 < r2 || r1 = r2

  def >= (r1,r2) = r2 >= r1

  def min(r1, r2) = if r1 >= r2 then r2 else r1
  def max(r1, r2) = if r1 <= r2 then r2 else r1

  % non-negative:

  op nonNegative? : Rational -> Boolean
  def nonNegative? r = r >= zero

  type NonNegativeRational = (Rational | nonNegative?)

  def abs r = if nonNegative? r then r else - r

  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal

  (* The following two ops have been moved into this spec from the base spec
  Integer. The two ops had no definition or axiom associated to them, and
  furthermore gcd(0,0) is not well defined in general; so they do not belong to
  a "good" library spec. They are nonetheless used in some specs in this
  directory, and so we put them here for now. There is handwritten Lisp code for
  them in ./Handwritten/Lisp/Rational.lisp, moved from
  Specware4Library/Base/Handwritten/Lisp. *)
  op Integer.gcd : Integer * Integer -> PosNat
  op Integer.lcm : Integer * Integer -> Nat

endspec
