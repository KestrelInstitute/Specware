(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Coef qualifying spec

  type CoefAux.Coef
  op zero: Coef
  op one: Coef
  op minusOne: Coef

  op equal: Coef * Coef -> Bool

  op nonNegative?: Coef -> Bool

  type CoefAux.NonNegativeCoef = (Coef | nonNegative?)

  op CoefAux.- : Coef -> Coef
  op +   infixl 25 : Coef * Coef -> Coef
  op -   infixl 25 : Coef * Coef -> Coef
  op *   infixl 27 : Coef * Coef -> Coef
  op <=  infixl 20 : Coef * Coef -> Bool
  op <   infixl 20 : Coef * Coef -> Bool
  op >=  infixl 20 : Coef * Coef -> Bool
  op >   infixl 20 : Coef * Coef -> Bool
  op abs           : Coef -> NonNegativeCoef
  op min           : Coef * Coef -> Coef
  op max           : Coef * Coef -> Coef
  op compare       : Coef * Coef -> Comparison
  op pred          : Nat -> Coef
  op toString      : Coef -> String

  op denominator   : Coef -> Coef


  op floor         : Coef -> Int
  op ceiling       : Coef -> Int
  op div infixl 26 : Coef * NonNegativeCoef -> Coef
  op rem infixl 26 : Coef * NonNegativeCoef -> Coef

  op Coef.gcd: Coef * Coef -> Coef

%  def gcd(i, j) =
%    toCoef(gcd(ratToInt(i), ratToInt(j)))

%  op lcm: Coef * Coef -> Coef
%  def lcm(i, j) =
%    toCoef(lcm(ratToInt(i), ratToInt(j)))

  op Integer.toInt  : Coef -> Int
  op Integer.toCoef : Int  -> Coef

endspec
