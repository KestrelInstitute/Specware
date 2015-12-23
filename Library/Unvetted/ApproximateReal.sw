(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
2005:03:17
LM
This is meant as a possible version of a spec
having (e.g.) the IEEE Floats as a model.

This requires that INF is mapped to the largest possible
true Float value (apparently 2**1024 - 2**971) and similarly
for -INF.  So each operation that could result in overflow
must check for this in an implementation based on IEEE Floats.

The purpose is to be able to prove some properties of
arithmetic expressions and such on real numbers, presumably
parametrized with things like "maxreal" and "maxrelerror",
without having to deal with the full complexity of the IEEE
standard.

*)

ApproximateReal qualifying spec
  import Rational

  type Real

  op +  infixl 25 : Real * Real -> Real
  op -  infixl 25 : Real * Real -> Real
  op *  infixl 27 : Real * Real -> Real
  op /  infixl 26 : Real * NonZeroReal -> Real
  op <= infixl 20 : Real * Real -> Bool
  op <  infixl 20 : Real * Real -> Bool
  op >= infixl 20 : Real * Real -> Bool
  op >  infixl 20 : Real * Real -> Bool
  op Real.-       : Real -> Real
  op abs          : Real -> NonNegativeReal
  op min          : Real * Real -> Real
  op max          : Real * Real -> Real
  op compare      : Real * Real -> Comparison

  op intToReal : Int  -> Real
  op floor     : Real -> Int
  op round     : Real -> Int
  op ceiling   : Real -> Int

  op ratToReal: Rational -> Real
  op realToRat: Real -> Rational

  axiom realToRatToReal is
    ratToReal o realToRat = id

  axiom ratToRealZero is
    ratToReal zero = zero

  axiom realToRatZero is
    realToRat zero = zero

  op realToString : Real -> String
  op toString : Real -> String
  def toString = realToString

  op zero: Real
  op one: Real

  op  nonZero? : Real -> Bool
  def nonZero? x = x ~= zero

  type NonZeroReal = (Real | nonZero?)

  op  nonNegative? : Real -> Bool
  def nonNegative? x = x >= zero

  type NonNegativeReal = (Real | nonNegative?)

  % Cannot use "the" closestTo since two values may be equally close
  op  closestTo infixl 0 : Real * Rational -> Bool
  def closestTo(x, r) = fa(x1 : Real)
                            abs(realToRat x - r) <= abs(realToRat x1 - r)

  def + (x,y) = the(z) z closestTo (realToRat x + realToRat y)
  def - (x,y) = the(z) z closestTo (realToRat x - realToRat y)
  def * (x,y) = the(z) z closestTo (realToRat x * realToRat y)
  def / (x,y) = the(z) z closestTo (realToRat x / realToRat y)

  def <  (x,y) = realToRat x < realToRat y
  def <= (x,y) = x < y || x = y
  def >= (x,y) = y >= x

  def Real.-x = zero-x

  def abs x = if nonNegative? x then x else -x

  def min(x,y) = if x < y then x else y
  def max(x,y) = if x > y then x else y

  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal

  def intToReal = ratToReal o intToRat

  axiom floorDef is
    fa(i : Int, x : Real)
      i <= floor x <=> intToRat i <= realToRat x

  axiom ceilingDef is
    fa(i : Int, x : Real)
      i >= ceiling x <=> intToRat i >= realToRat x

endspec
