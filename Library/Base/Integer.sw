Integer qualifying spec

  import Nat, Compare, Functions

  type Integer.Integer  % qualifier required for internal parsing reasons

  % true for non-negative integers:
  op natural? : Integer -> Boolean
  def natural? i = 0 <= i

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
     % qualifier needed to avoid confusion with Integer.-, the binary minus.

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
    bijective? IntegerAux.-

  type NonZeroInteger = {i : Integer | i ~= 0}

  % other ops on integers:

  op +   infixl 25 : Integer * Integer -> Integer
  op -   infixl 25 : Integer * Integer -> Integer
  op *   infixl 27 : Integer * Integer -> Integer
  op div infixl 26 : Integer * NonZeroInteger -> Integer
  op rem infixl 26 : Integer * NonZeroInteger -> Integer
  op <=  infixl 20 : Integer * Integer -> Boolean
  op <   infixl 20 : Integer * Integer -> Boolean
  op >=  infixl 20 : Integer * Integer -> Boolean
  op >   infixl 20 : Integer * Integer -> Boolean
  op abs           : Integer -> Nat
  op min           : Integer * Integer -> Integer
  op max           : Integer * Integer -> Integer
  op compare       : Integer * Integer -> Comparison
  op pred          : Nat -> Integer
  op gcd           : Integer * Integer -> PosNat
  op lcm           : Integer * Integer -> Nat

  def >= (x,y) = y <= x

  def > (x,y) = y <  x

  def abs x = if x >= 0 then x else - x
  proof Isa [simp] end-proof

  def min(x,y) = if x < y then x else y

  def max(x,y) = if x > y then x else y

  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal

  def pred x = x - 1

  axiom addition_def1 is
    fa(i:Integer) i+0 = i && 0+i = i
  axiom addition_def2 is
    fa(n1:PosNat, n2:PosNat)
           n1  +   n2  = plus(n1,n2)
      && (-n1) + (-n2) = -(plus(n1,n2))
      &&   n1  + (-n2) = (if lte(n1,n2) then -(minus(n2,n1))
                                        else minus(n1,n2))
      && (-n1) +   n2  = (if lte(n1,n2) then minus(n2,n1)
                                        else -(minus(n1,n2)))

  axiom subtraction_def is
    fa (x:Integer, y:Integer) (x - y) = x + (- y)

  axiom multiplication_def is
    fa (x:Integer, y:Integer) 0 * y = 0
                       && (x+1) * y = x * y + y
                       && (x-1) * y = x * y - y
    % since every integer is reachable from 0 by adding or subtracting 1
    % zero or more times, this axiom completely defines multiplication

  axiom division_def is
    fa (x:Integer, y:NonZeroInteger, z:Integer)
       % truncate result of exact division towards 0:
       x div y = z <=> abs z = abs x div abs y  % abs of result
                     && (x * y >= 0 => z >= 0)  % sign of
                     && (x * y <= 0 => z <= 0)  % result

  axiom remainder_def is
    fa (x:Integer, y:NonZeroInteger)
       x rem y = x - y * (x div y)

  axiom less_than_equal_def is
    fa (x:Integer, y:Integer) x <= y <=> natural? (y - x)

  axiom less_than_def is
    fa (x:Integer, y:Integer) x < y <=> (x <= y && x ~= y)

  proof Isa Thy_Morphism Presburger
   type Integer.Integer \_rightarrow int
   type Nat.Nat -> nat (int,nat) [+,*,div,rem,<=,<,>=,>,abs,min,max]
   Integer.+ \_rightarrow +  Left 25
   Integer.- \_rightarrow -  Left 25
   IntegerAux.- \_rightarrow -
   Integer.~ \_rightarrow -
   Integer.* \_rightarrow *  Left 27
   Integer.div \_rightarrow div  Left 26
   Integer.rem \_rightarrow mod  Left 26
   Integer.<= \_rightarrow \<le>  Left 20
   Integer.< \_rightarrow <  Left 20
   Integer.>= \_rightarrow \<ge>  Left 20
   Integer.> \_rightarrow >  Left 20
   Integer.min \_rightarrow min curried
   Integer.max \_rightarrow max curried
  end-proof

endspec
