Integer qualifying spec

  import Nat, Compare, Functions

  type Integer.Integer  % qualifier required for internal parsing reasons

  % true for non-negative integers:
  op natural? : Integer -> Boolean

  (* The following type definition defines the naturals to be a subtype of the
  integers. However, since the naturals have been axiomatized in spec Nat,
  this definition really constrains the integers to be a supertype of the
  naturals. In addition, it allows us to take advantage of the automatic
  insertions of relax and restrict to map between naturals and integers. Note
  that the qualifier Nat in Nat.Nat is needed because otherwise the following
  type definition would introduce a new unqualified type Nat. *)

  type Nat.Nat = (Integer | natural?)

  % unary minus:
  op IntegerAux.- : Integer -> Integer
     % qualifier needed to avoid confusion with binary -;
     % ending "_" to avoid conflicts with user-defined qualifiers

  % for backward compatibility:
  op Integer.~ : Integer -> Integer
     % qualifier required to avoid parsing confusion with boolean negation ~
  axiom backward_compatible_unary_minus_def is
    fa (i: Integer) Integer.~(i) = -(i)

  % negative integers are obtained by negating positive ones:
  axiom negative_integers is
    fa(i:Integer) ~(natural? i) => (ex(n:PosNat) i = -n)

  % negating a positive integer yields a negative integer:
  axiom negative is
    fa(n:PosNat) ~(natural? (- n))

  % negating distinct positive integers yield distinct negative ones:
  axiom unary_minus_injective_on_positives is
    fa(n1:PosNat, n2:PosNat) n1 ~= n2 => -n1 ~= -n2

  % negating a negative integer yields the positive one we started from:
  axiom minus_negative is
    fa(n:PosNat) -(-n) = n

  % negating zero is a no-op
  axiom minus_zero is
    -0 = 0

  theorem unary_minus_involution is
    fa(i:Integer) -(-i) = i

  theorem unary_minus_bijective is
    bijective? -

  type NonZeroInteger = {i : Integer | i ~= 0}

  % other ops on integers:

  op abs : Integer -> Nat
  def abs x = if x >= 0 then x else - x

  op + infixl 25 : Integer * Integer -> Integer
  def + = the (fn (add : Integer * Integer -> Integer) ->
    (fa(i:Integer) add(i,0) = i && add(0,i) = i)
    &&
    (fa(n1:PosNat, n2:PosNat)
          add( n1, n2) = plus(n1,n2)
       && add(-n1,-n2) = -(plus(n1,n2))
       && add( n1,-n2) = (if lte(n1,n2) then -(minus(n2,n1))
                                        else minus(n1,n2))
       && add(-n1, n2) = (if lte(n1,n2) then minus(n2,n1)
                                        else -(minus(n1,n2)))))

  op - infixl 25 : Integer * Integer -> Integer
  def - (x,y) = x + (- y)

  op * infixl 27 : Integer * Integer -> Integer
  def * = the (fn (mul : Integer * Integer -> Integer) ->
    fa (x:Integer, y:Integer) mul (0, y) = 0
                           && mul (x+1, y) = mul (x, y) + y
                           && mul (x-1, y) = mul (x, y) - y)
    % since every integer is reachable from 0 by adding or subtracting 1
    % zero or more times, the formula above completely defines multiplication

  op div infixl 26 : Integer * NonZeroInteger -> Integer
  def div = the (fn (div : Integer * NonZeroInteger -> Integer) ->
    fa (x:Integer, y:NonZeroInteger, z:Integer)
       % truncate result of exact division towards 0:
       div (x, y) = z <=> abs z = div (abs x, abs y)  % abs of result
                       && (x * y >= 0 => z >= 0)  % sign of
                       && (x * y <= 0 => z <= 0)) % result

  op rem infixl 26 : Integer * NonZeroInteger -> Integer
  def rem = the (fn (rem : Integer * NonZeroInteger -> Integer) ->
    fa (x:Integer, y:NonZeroInteger)
       rem (x, y) = x - y * (x div y))

  op <= infixl 20 : Integer * Integer -> Boolean
  def <= (x,y) = natural? (y - x)

  theorem natural?_and_less_than_equal is
    fa(i:Integer) natural? i <=> 0 <= i

  op < infixl 20 : Integer * Integer -> Boolean
  def < (x,y) = (x <= y && x ~= y)

  op >= infixl 20 : Integer * Integer -> Boolean
  def >= (x,y) = y <= x

  op > infixl 20 : Integer * Integer -> Boolean
  def > (x,y) = y <  x

  op min : Integer * Integer -> Integer
  def min(x,y) = if x < y then x else y

  op max : Integer * Integer -> Integer
  def max(x,y) = if x > y then x else y

  op compare : Integer * Integer -> Comparison
  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal

  op pred : Nat -> Integer
  def pred x = x - 1

endspec
