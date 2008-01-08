Integer qualifying spec

  import Compare, Functions

  (* We introduce integers via a Peano-like axiomatization. Intuitively, Peano's
  axioms for the natural numbers state that natural numbers form a chain that
  starts with 0 and proceeds via the successor function, that the chain never
  crosses itself (either at 0 or at any other natural number), and that there
  are no natural numbers outside the chain. Integers form a chain that has 0 as
  its "middle" point and that proceeds forward and backward via the successor
  and predecessor functions. Thus, it suffices to introduce a constant for 0,
  and a bijective successor function. Bijectivity implies that there is an
  inverse, which is the predecessor function. Bijectivity also implies that the
  bidirectionally infinite chain of integers never crosses itself. To complete
  the axiomatization, we need an induction-style axiom stating that there are no
  integers ouside the chain. The induction principle is the following: prove P
  for 0 and prove that P is preserved by both successor and predecessor (this
  ensures that we "reach" every integer). *)

  type Integer

  op zero : Integer

  op succ : Bijection (Integer, Integer)

  axiom induction is
    fa (p : Integer -> Boolean)
      p zero &&
      (fa(i) p i => p (succ i) && p (inverse succ i)) =>
      (fa(i) p i)

  % we name the predecessor function, which is the inverse of succ:

  op pred : Bijection (Integer, Integer) = inverse succ

  % number 1:

  op one : Integer = succ zero

  (* We now define three predicates that partition the integers into 0, positive
  integers, and negative integers. We define positive integers inductively: 1 is
  positive, and if i is positive then succ i is positive.  This is expressed by
  the higher-order predicate satisfiesInductiveDef?, which is locally defined in
  the definition of op positive? below. The definition is inductive in the sense
  that positive? must be the smallest predicate that satisfies that definition.
  This is expressed by saying that for every other predicate p? that satisfies
  the inductive definition, positive? is smaller than p?, i.e. all integers in
  positive? are also in p?. *)

  op zero? (i:Integer) : Boolean = (i = zero)

  op positive? : Integer -> Boolean = the(positive?)
    let def satisfiesInductiveDef? (p? : Integer -> Boolean) : Boolean =
        p? one &&
        (fa(i) p? i => p? (succ i)) in
    satisfiesInductiveDef? positive? &&
    (fa(p?) satisfiesInductiveDef? p? =>
            (fa(i) positive? i => p? i))

  op negative? (i:Integer) : Boolean = ~ (positive? i) && ~ (zero? i)

  (* The following ops are inductively defined on the integers. They distinguish
  among 0, positive, and negative integers. *)

  % unary minus (qualifier avoids confusion with binary minus):

  op IntegerAux.- : Bijection (Integer, Integer) = the(minus)
                          minus zero = zero &&
    (fa(i) positive? i => minus i    = pred (minus (pred i))) &&
    (fa(i) negative? i => minus i    = succ (minus (succ i)))

  % legacy synonym (qualifier avoids confusion with boolean negation):

  op Integer.~ : Bijection (Integer, Integer) = -

  % addition:

  op + infixl 25 : Integer * Integer -> Integer = the(plus)
    (fa(j)                  plus (zero, j) = j) &&
    (fa(i,j) positive? i => plus (i,    j) = succ (plus (pred i, j))) &&
    (fa(i,j) negative? i => plus (i,    j) = pred (plus (succ i, j)))

  % subtraction:

  op - (i:Integer, j:Integer) infixl 25 : Integer = i + (- j)

  % multiplication:

  op * infixl 27 : Integer * Integer -> Integer = the(times)
    (fa(j)                  times (zero, j) = zero) &&
    (fa(i,j) positive? i => times (i,    j) = times (pred i, j) + j) &&
    (fa(i,j) negative? i => times (i,    j) = times (succ i, j) - j)

  % relational operators:

  op < (i:Integer, j:Integer) infixl 20 : Boolean = negative? (i - j)

  op > (i:Integer, j:Integer) infixl 20 : Boolean = j < i

  op <= (i:Integer, j:Integer) infixl 20 : Boolean = i < j || i = j

  op >= (i:Integer, j:Integer) infixl 20 : Boolean = i > j || i = j

  theorem <=_and_>=_are_converses is
    fa (i:Integer, j:Integer) (i <= j) = (j >= i)

  % absolute value:

  op abs (i:Integer) : {j:Integer | j >= zero} = if i >= zero then i else (- i)

  % subtype for non-zero integers (useful to define division):

  type NonZeroInteger = {i:Integer | i ~= zero}

  (* We define integer division to truncate towards 0 (the other possibility
  is towards minus-infinity). This means that: the absolute value of the
  quotient q is the (unique) Q such that I = J * Q + r, where I = abs i, J =
  abs j, and 0 <= r < J; and the sign of q coincides with the sign of i * j
  (i.e. positive if i and j are both positive or negative, negative if i is
  positive/negative and j is negative/positive, and 0 if i is 0). *)

  op div (i:Integer, j:NonZeroInteger) infixl 26 : Integer = the(q)
    (ex(r) abs i = abs j * abs q + r && zero <= r && r < abs j) &&
    (i * j >= zero => q >= zero) &&
    (i * j <= zero => q <= zero)

  % better synonym:

  op / infixl 26 : Integer * NonZeroInteger -> Integer = div

  % we define remainder in such a way that i = j * (i div j) + (i rem j):

  op rem (i:Integer, j:NonZeroInteger) infixl 26 : Integer = i - j * (i / j)

  % min and max:

  op min (i:Integer, j:Integer) : Integer = if i < j then i else j

  op max (i:Integer, j:Integer) : Integer = if i > j then i else j

  % comparison:

  op compare (i:Integer, j:Integer) : Comparison = if i < j then Less
                                              else if i > j then Greater
                                              else (* i = j *)   Equal

  (* The following predicate captures the notion that x evenly divides y without
  leaving a remainder (sometimes denoted "x|y"; note that "|" is disallowed as a
  Metaslang name), or equivalently that x is a factor of y, i.e. that y can be
  expressed as x * z for some integer z. *)

  op divides (x:Integer, y:Integer) infixl 20 : Boolean =
    ex(z:Integer) x * z = y

  (* If x is not 0, the notion is equivalent to saying that the remainder of the
  division of y by x is 0. *)

  theorem non_zero_divides_iff_zero_remainder is
    fa (x:NonZeroInteger, y:Integer) x divides y <=> y rem x = zero
  proof Isa
    sorry
  end-proof

  (* Obviously, any integer divides 0. *)

  theorem any_divides_zero is
    fa(x:Integer) x divides zero
  proof Isa
    apply(simp add: Integer__divides_def)
  end-proof

  (* Only 0 is divided by 0, because multiplying . *)

  theorem only_zero_is_divided_by_zero is
    fa(x:Integer) zero divides x => x = zero
  proof Isa
      apply(simp add: Integer__divides_def)
  end-proof

  (* Since the division and remainder operations are not defined for non-zero
  divisors (see ops div and rem above), it may seem odd that our definition
  allows 0 to "divide" anything at all. The reason why, according to our
  definition, 0 can be a "divisor" is that we have not used the division
  operation to define the notion, but instead we have used multiplication. The
  use of multiplication is consistent with the general definition of "divisors"
  in rings (integers form a ring), which is exactly defined in terms of the
  multiplicative operation of the ring, as above. The definition in terms of
  multiplication enables an elegant definition of greatest common divisor
  (g.c.d.) and least common multiple (l.c.m.), below. *)

  (* The notion of being a multiple is the converse of the "divides" relation: x
  is a multiple of y iff x = z * y for some integer z. *)

  op multipleOf (x:Integer, y:Integer) infixl 20 : Boolean = y divides x

  (* It is well known that the "divides" ordering relation induces a complete
  lattice structure on the natural numbers, with 1 bottom, 0 top, g.c.d. as
  meet, and l.c.m. as join. So we define ops gcd and lcm as meet and join. Note
  that we restrict the result to be a natural number. *)

  op gcd (x:Integer, y:Integer) : {z:Integer | z >= zero} =
    the(z:Integer)
    % z is non-negative and divides both x and y:
       z >= zero && z divides x && z divides y &&
    % and is divided by any integer that also divides x and y:
       (fa(w:Integer) w divides x && w divides y => w divides z)

  op lcm (x:Integer, y:Integer) : {z:Integer | z >= zero} =
    the(z:Integer)
    % z is non-negative and is a multiple of both x and y:
       z >= zero && z multipleOf x && z multipleOf y &&
    % and any integer that is a multiple of x and y is also a multiple of z:
       (fa(w:Integer) w multipleOf x && w multipleOf y => z multipleOf w)

  (* If x and y are not both 0, their g.c.d. is positive and is the largest
  integer (according to the usual ordering on the integers) that divides both x
  and y. If x = y = 0, their g.c.d. is 0. *)

  theorem gcd_of_not_both_zero is
    fa(x:Integer,y:Integer) x ~= zero || y ~= zero =>
      gcd(x,y) > zero &&
      gcd(x,y) divides x && gcd(x,y) divides y &&
      (fa(w:Integer) w divides x && w divides y => gcd(x,y) >= w)
  proof Isa
    sorry
  end-proof

  theorem gcd_of_zero_zero_is_zero is
    gcd (zero, zero) = zero
  proof Isa
    sorry
  end-proof

  (* The l.c.m. of x and y is the smallest multiple, in absolute value, among
  all the multiples of x and y. The absolute value restriction is important,
  because otherwise the l.c.m. would always be negative (or 0, if x = y = 0). *)

  theorem lcm_smallest_abs_multiple is
    fa (x:Integer, y:Integer, w:Integer)
      w multipleOf x && w multipleOf y => lcm(x,y) <= abs w
  proof Isa
    sorry
  end-proof

  % mapping to Isabelle:

  proof Isa Thy_Morphism Presburger
   type Integer.Integer -> int
   Integer.zero         -> 0
   Integer.one          -> 1
   IntegerAux.-         -> -
   Integer.~            -> -
   Integer.+            -> +     Left 25
   Integer.-            -> -     Left 25
   Integer.*            -> *     Left 27
   Integer.<=           -> \<le> Left 20
   Integer.<            -> <     Left 20
   Integer.>=           -> \<ge> Left 20
   Integer.>            -> >     Left 20
   Integer.div          -> div   Left 26
   Integer.rem          -> mod   Left 26
   Integer.min          -> min curried
   Integer.max          -> max curried
  end-proof

endspec
