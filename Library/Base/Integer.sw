Integer qualifying spec

  import Compare

  % sorts:

 %sort Integer
  sort NonZeroInteger = {i : Integer | ~(i = 0)}

  % ops whose Lisp code is hand-written:

 %op ~             : Integer -> Integer
 %op +   infixl 25 : Integer * Integer -> Integer
  op -   infixl 25 : Integer * Integer -> Integer
  op *   infixl 27 : Integer * Integer -> Integer
  op div infixl 26 : Integer * NonZeroInteger -> Integer
  op rem infixl 26 : Integer * NonZeroInteger -> Integer
 %op <   infixl 20 : Integer * Integer -> Boolean
  op <=  infixl 20 : Integer * Integer -> Boolean

  axiom subtraction_def is
    fa (x,y : Integer) (x - y) = x + (~y)

  axiom multiplication_def is
    fa (x,y : Integer) 0 * y = 0
                     & (x+1) * y = x * y + y
                     & (x-1) * y = x * y - y
    % since every integer is reachable from 0 by adding or subtracting 1
    % zero or more times, this axiom completely defines multiplication

  axiom division_def is
    fa (x : Integer, y : NonZeroInteger, z : Integer)
       % truncate result of exact division towards 0:
       x div y = z <=> abs z = abs x div abs y  % abs of result
                     & (x * y >= 0 => z >= 0)  % sign of
                     & (x * y <= 0 => z <= 0)  % result

  axiom remainder_def is
    fa (x : Integer, y : NonZeroInteger)
       x rem y = x - y * (x div y)

  axiom less_than_equal_def is
    fa (x,y : Integer) x <= y <=> (x < y or x = y)

  % ops whose Lisp code is generated:

  op >  infixl 20 : Integer * Integer -> Boolean
  op >= infixl 20 : Integer * Integer -> Boolean
  op abs          : Integer -> Integer
  op min          : Integer * Integer -> Integer
  op max          : Integer * Integer -> Integer
  op compare      : Integer * Integer -> Comparison

  def > (x,y) = y <  x

  def >= (x,y) = y <= x

  def abs x = if x >= 0 then x else ~x

  def min(x,y) = if x < y then x else y

  def max(x,y) = if x > y then x else y

  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op toString    : Integer -> String  % deprecated
  % op show        : Integer -> String
  % op intToString : Integer -> String
  % op stringToInt : (String | ...) -> Integer

endspec
