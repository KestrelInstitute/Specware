Coef qualifying spec

  type Coef_.Coef
  op zero: Coef
  op one: Coef
  op minusOne: Coef

  op equal: Coef * Coef -> Boolean

  op nonNegative?: Coef -> Boolean

  type Coef_.NonNegativeCoef = (Coef | nonNegative?)

  op Coef_.- : Coef -> Coef
  op +   infixl 25 : Coef * Coef -> Coef
  op -   infixl 25 : Coef * Coef -> Coef
  op *   infixl 27 : Coef * Coef -> Coef
  op <=  infixl 20 : Coef * Coef -> Boolean
  op <   infixl 20 : Coef * Coef -> Boolean
  op >=  infixl 20 : Coef * Coef -> Boolean
  op >   infixl 20 : Coef * Coef -> Boolean
  op abs           : Coef -> NonNegativeCoef
  op min           : Coef * Coef -> Coef
  op max           : Coef * Coef -> Coef
  op compare       : Coef * Coef -> Comparison
  op pred          : Nat -> Coef
  op toString      : Coef -> String

  op denominator   : Coef -> Coef


  op floor         : Coef -> Integer
  op ceiling       : Coef -> Integer
  op div infixl 26 : Coef * NonNegativeCoef -> Coef
  op rem infixl 26 : Coef * NonNegativeCoef -> Coef

  op Coef.gcd: Coef * Coef -> Coef

%  def gcd(i, j) =
%    toCoef(gcd(ratToInt(i), ratToInt(j)))

%  op lcm: Coef * Coef -> Coef
%  def lcm(i, j) =
%    toCoef(lcm(ratToInt(i), ratToInt(j)))

  op Integer.toInt: Coef -> Integer
  op Integer.toCoef: Integer -> Coef

endspec
