% October 21, 2005
% Lindsay
% For MXJ.

% This .sw file is not used by MXJ but the corresponding runtime in
% Handwritten/Lisp is.

Complex qualifying spec
  import Pretty
  import Double

  op String.toComplex : String -> Complex
  op Integer.toComplex: Integer -> Complex
  op Double.toComplex: Double -> Complex

  op Complex.toString : Complex -> String

  op Double.complex : Double * Double -> Complex
  op Integer.complex : Integer * Integer -> Complex

  op Complex_.- : Complex -> Complex

  op + infixl 25 : Complex * Complex -> Complex
  op - infixl 25 : Complex * Complex -> Complex

  op * infixl 27 : Complex * Complex -> Complex

  op zero : Complex

  type NonZeroComplex = {r : Complex | r ~= zero}

  op inv : NonZeroComplex -> NonZeroComplex
  op / infixl 26 : Complex * NonZeroComplex -> Complex

  % comparisons:

  op < infixl 20 : Complex * Complex -> Boolean
  op > infixl 20 : Complex * Complex -> Boolean
  op <= infixl 20 : Complex * Complex -> Boolean
  op >= infixl 20 : Complex * Complex -> Boolean

  % non-negative:

  op nonNegative? : Complex -> Boolean
  def nonNegative? r = r >= zero

  type NonNegativeComplex = (Complex | nonNegative?)

  op abs : Complex -> NonNegativeComplex

  op sin : Complex -> Complex   % in radians
  op cos : Complex -> Complex   % in radians
  op tan : Complex -> Complex   % in radians

  op asin : Complex -> Complex   % in radians
  op acos : Complex -> Complex   % in radians
  op atan : Complex -> Complex   % in radians

  op sqrt : Complex -> Complex 

  op ceiling : Complex -> Integer
  op floor : Complex -> Integer

  op imag : Complex -> Double
  op real : Complex -> Double

  op pp : Complex -> Pretty
  def pp cmpx = pp (toString cmpx)
endspec

