(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% October 21, 2005
% Lindsay
% For MXJ.

% This .sw file is not used by MXJ but the corresponding runtime in
% Handwritten/Lisp is. 

Double qualifying spec
  %import /Library/PrettyPrinter/BjornerEspinosa

  type Double 

  op Integer.toDouble : Int    -> Double
  op String.toDouble  : String -> Double

  op show : Double -> String

  op DoubleAux.- : Double -> Double

  op + infixl 25 : Double * Double -> Double
  op - infixl 25 : Double * Double -> Double

  op * infixl 27 : Double * Double -> Double

  op sq(x: Double): Double = x * x

  op zero : Double
  op Pi: Double

  type NonZeroDouble = {r : Double | r ~= zero}
  op / infixl 26 : Double * NonZeroDouble -> Double

  op inv : NonZeroDouble -> NonZeroDouble

  op mod infixl 26: Double * NonZeroDouble -> Double

  op DoubleInt.+ infixl 25 : Double * Int -> Double
  op DoubleInt.- infixl 25 : Double * Int -> Double
  op DoubleInt.* infixl 27 : Double * Int -> Double
  op DoubleInt./ infixl 26 : Double * Int0 -> Double

  op IntDouble.+ infixl 25 : Int * Double -> Double
  op IntDouble.- infixl 25 : Int * Double -> Double
  op IntDouble.* infixl 27 : Int * Double -> Double


  % comparisons:

  op <  infixl 20 : Double * Double -> Bool
  op >  infixl 20 : Double * Double -> Bool
  op <= infixl 20 : Double * Double -> Bool
  op >= infixl 20 : Double * Double -> Bool

  % non-negative:

  op nonNegative? : Double -> Bool
  def nonNegative? r = r >= zero

  type NonNegativeDouble = (Double | nonNegative?)

  op abs : Double -> NonNegativeDouble

  op sin : Double -> Double   % in radians
  op cos : Double -> Double   % in radians
  op tan : Double -> Double   % in radians

  op asin : Double -> Double   % in radians
  op acos : Double -> Double   % in radians
  op atan : Double -> Double   % in radians
  op DoubleAux.atan : Double * Double -> Double

%  op sqrt : Double -> Complex 
  op sqrt: NonNegativeDouble -> NonNegativeDouble

  op ceiling : Double -> Int
  op floor   : Double -> Int

  %op pp : Double -> Pretty
  %def pp dbl = pp (show dbl)
endspec

