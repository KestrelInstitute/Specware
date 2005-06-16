PrInteger qualifying spec

  import ../Base/Integer

  %type Integer.Integer  % qualifier required for internal parsing reasons

  % true for non-negative integers:
  %op natural? : Integer -> Boolean

  (* The following type definition defines the naturals to be a subtype of the
  integers. However, since the naturals have been axiomatized in spec Nat,
  this definition really constrains the integers to be a supertype of the
  naturals. In addition, it allows us to take advantage of the automatic
  insertions of relax and restrict to map between naturals and integers. Note
  that the qualifier Nat in Nat.Nat is needed because otherwise the following
  type definition would introduce a new unqualified type Nat. *)

  %type Nat.Nat = (Integer | natural?)

  % unary minus:
  %op Integer_.- : Integer -> Integer
     % qualifier needed to avoid confusion with binary -;
     % ending "_" to avoid conflicts with user-defined qualifiers

  % for backward compatibility:
  %op Integer.~ : Integer -> Integer
     % qualifier required to avoid parsing confusion with boolean negation ~
  axiom backward_compatible_unary_minus_def is
    fa (i: Integer) Integer.~ i = - i

  axiom natural?_def is
    fa (i: Integer) natural?(i) <=> i >= 0

  % negative integers are obtained by negating positive ones:
  axiom negative_integers is
    fa(i:Integer) ~(natural? i) => (ex(n:PosNat) i = -n)

  axiom negative is
    fa(n:PosNat) ~(natural? (- n))

  % negating distinct positive integers yield distinct negative ones:
  axiom unary_minus_injective_on_positives is
    fa(n1:PosNat, n2:PosNat) n1 ~= n2 => -n1 ~= -n2

  % negating zero is a no-op
  axiom minus_zero is
    -0 = 0

  theorem unary_minus_involution is
    fa(i:Integer) -(-i) = i

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

  theorem natural?_and_less_than_equal is
    fa(i:Integer) natural? i <=> 0 <= i

  axiom less_than_def is
    fa (x:Integer, y:Integer) x < y <=> (x <= y && x ~= y)

  axiom greater_than_equal_def is
    fa (x:Integer, y:Integer) (>= (x,y)) = (y <= x)

  axiom greater_than_def is
    fa (x:Integer, y:Integer) > (x,y) = (y <  x)

  axiom abs_def is
    fa (x: Integer) x >= 0 => abs(x) = x

  axiom abs_def is
    fa (x: Integer) ~(x >= 0) => abs(x) = -x

  axiom min_def is
    fa (x:Integer, y:Integer) x < y => min(x,y) = x

  axiom min_def is
    fa (x:Integer, y:Integer) ~(x < y) => min(x,y) = y

  axiom max_def is
    fa (x:Integer, y:Integer) x < y => max(x,y) = y

  axiom max_def is
    fa (x:Integer, y:Integer) ~(x < y) => max(x,y) = x

  axiom compare_def is
    fa (x:Integer, y:Integer)
     x < y => compare(x, y) = Less

  axiom compare_def is
    fa (x:Integer, y:Integer)
       x > y => compare(x,y) = Greater

  axiom compare_def is
    fa (x:Integer, y:Integer)
       x = y => compare(x,y) = Equal

  axiom pred_def is
     fa (x: Integer) pred x = x - 1

%  axiom less_less_equal is
%     fa(x: Integer,y: Integer) x < y  <=> x+1 <= y

%  axiom plus_gt_zero is fa(x,y,z,w) x + y <= z && 0 <= y => x <= z

  axiom plus_minus is fa(x,y,z) x+y = z <=>  x = z-y

%  axiom plus_greater_equal is
%     fa (x: Integer, y: Integer, z: Integer) x >= z && y >= z => x + y >= z

  axiom plus_greater_chain is
     fa (x: Integer, y: Integer, z: Integer) x + y >= 0 && (- y) + z >= 0 => x + z >= 0


endspec
