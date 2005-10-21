% October 21, 2005
% Lindsay
% For MXJ.

% This .sw file is not used by MXJ but the corresponding runtime in
% Handwritten/Lisp is. 

Double qualifying spec
  import Pretty

  type Double 
  type Complex.Complex

  op Integer.toDouble : Integer -> Double
 
  op String.toDouble : String -> Double
  op Double.toString : Double -> String

  op Double_.- : Double -> Double

  op + infixl 25 : Double * Double -> Double
  op - infixl 25 : Double * Double -> Double

  op * infixl 27 : Double * Double -> Double

  op zero : Double

  type NonZeroDouble = {r : Double | r ~= zero}

  op inv : NonZeroDouble -> NonZeroDouble
  op / infixl 26 : Double * NonZeroDouble -> Double

  % comparisons:

  op < infixl 20 : Double * Double -> Boolean
  op > infixl 20 : Double * Double -> Boolean
  op <= infixl 20 : Double * Double -> Boolean
  op >= infixl 20 : Double * Double -> Boolean

  % non-negative:

  op nonNegative? : Double -> Boolean
  def nonNegative? r = r >= zero

  type NonNegativeDouble = (Double | nonNegative?)

  op abs : Double -> NonNegativeDouble

  op sin : Double -> Double   % in radians
  op cos : Double -> Double   % in radians
  op tan : Double -> Double   % in radians

  op asin : Double -> Double   % in radians
  op acos : Double -> Double   % in radians
  op atan : Double -> Double   % in radians

  op sqrt : Double -> Complex 

  op ceiling : Double -> Integer
  op floor : Double -> Integer

  op pp : Double -> Pretty
  def pp dbl = pp (toString dbl)
endspec

