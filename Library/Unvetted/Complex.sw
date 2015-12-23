(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% October 21, 2005
% Lindsay
% For MXJ.

% This .sw file is not used by MXJ but the corresponding runtime in
% Handwritten/Lisp is.

Complex qualifying spec
%  import Pretty
  import /Library/Unvetted/Double

  type Complex

  op String.toComplex  : String -> Complex
  op Integer.toComplex : Int    -> Complex
  op Double.toComplex  : Double -> Complex

  op show : Complex -> String

  op Double.complex  : Double * Double -> Complex
  op Integer.complex : Int    * Int    -> Complex

  op ComplexAux.- : Complex -> Complex

  op + infixl 25 : Complex * Complex -> Complex
  op - infixl 25 : Complex * Complex -> Complex

  op * infixl 27 : Complex * Complex -> Complex

  op zero : Complex

  type NonZeroComplex = {r : Complex | r ~= zero}

  op inv : NonZeroComplex -> NonZeroComplex
  op / infixl 26 : Complex * NonZeroComplex -> Complex

  % comparisons:

  op <  infixl 20 : Complex * Complex -> Bool
  op >  infixl 20 : Complex * Complex -> Bool
  op <= infixl 20 : Complex * Complex -> Bool
  op >= infixl 20 : Complex * Complex -> Bool

  % non-negative:

  op nonNegative? : Complex -> Bool
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

  op ceiling : Complex -> Int
  op floor   : Complex -> Int

  op imag : Complex -> Double
  op real : Complex -> Double

%  op pp : Complex -> Pretty
%  def pp cmpx = pp (toString cmpx)
endspec

