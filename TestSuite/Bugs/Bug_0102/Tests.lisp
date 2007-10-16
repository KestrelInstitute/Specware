(test-directories ".")

(test 

 ("Bug 0102 : Extra variable in gnerated proof obligation [see test for 0101]"
  :show   "ObligationsOfInteger.sw" 
  ;; expected output is the same as for test 101
  :output '(";;; Elaborating obligator at $TESTDIR/ObligationsOfInteger"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec  "
	    " import Compare"
	    " import Functions"
	    " type Integer"
	    " "
	    " op  zero : Integer"
	    " op  succ : Functions.Bijection(Integer, Integer)"
	    " axiom Integer.induction is "
	    "    fa(p : Integer -> Boolean) "
	    "     p(zero) "
	    "     && (fa(i : Integer) "
	    "          (p i => p(succ i) && p(Functions.inverse(succ) i))) "
	    "     => (fa(i : Integer) p i)"
	    " "
	    " op  pred : Functions.Bijection(Integer, Integer) = Functions.inverse(succ)"
	    " "
	    " op  one : Integer = succ(zero)"
	    " "
	    " op  zero? (i : Integer) : Boolean = i = zero"
	    " op  positive? : Integer -> Boolean"
	    " conjecture Integer.positive?_Obligation_the is "
	    "    ex1(positive? : Integer -> Boolean) "
	    "     let def satisfiesInductiveDef? p? = "
	    "           p?(one) && (fa(i : Integer) (p? i => p?(succ i)))"
	    "     in "
	    "     satisfiesInductiveDef? positive? "
	    "     && (fa(p?_1 : Integer -> Boolean, i_1 : Integer) "
	    "          (satisfiesInductiveDef? p?_1 && positive? i_1 => p?_1 i_1))"
	    " "
	    " def positive? = "
	    "   the (positive? : Integer -> Boolean) "
	    "    let def satisfiesInductiveDef? p? = "
	    "          p?(one) && (fa(i : Integer) (p? i => p?(succ i)))"
	    "    in "
	    "    satisfiesInductiveDef? positive? "
	    "    && (fa(p? : Integer -> Boolean) "
	    "         (satisfiesInductiveDef? p? "
	    "         => (fa(i : Integer) positive? i => p? i)))"
	    " "
	    " op  negative? (i : Integer) : Boolean = ~(positive? i) && ~(zero? i)"
	    " op  - : Functions.Bijection(Integer, Integer)"
	    " conjecture IntegerAux.-_Obligation_the is "
	    "    ex1(minus : Functions.Bijection(Integer, Integer)) "
	    "     minus(0) = 0 "
	    "     && (fa(i : Integer) "
	    "          (positive? i => minus i = pred(minus(pred i)))) "
	    "        && (fa(i_1 : Integer) "
	    "             (negative? i_1 => minus i_1 = succ(minus(succ i_1))))"
	    " "
	    " def - = "
	    "   the (minus : Functions.Bijection(Integer, Integer)) "
	    "    minus(zero) = zero "
	    "    && (fa(i : Integer) (positive? i => minus i = pred(minus(pred i)))) "
	    "       && (fa(i : Integer) "
	    "            (negative? i => minus i = succ(minus(succ i))))"
	    " "
	    " op  ~ : Functions.Bijection(Integer, Integer) = -"
	    " op  + infixl 25 : Integer * Integer -> Integer"
	    " conjecture Integer.+_Obligation_the is "
	    "    ex1(plus : Integer * Integer -> Integer) "
	    "     (fa(j : Integer) plus(0, j) = j) "
	    "     && (fa(i : Integer, j_1 : Integer) "
	    "          (positive? i => plus(i, j_1) = succ(plus(pred i, j_1)))) "
	    "        && (fa(i_1 : Integer, j_2 : Integer) "
	    "             (negative? i_1 "
	    "             => plus(i_1, j_2) = pred(plus(succ i_1, j_2))))"
	    " "
	    " def + = "
	    "   the (plus : Integer * Integer -> Integer) "
	    "    (fa(j : Integer) plus(zero, j) = j) "
	    "    && (fa(i : Integer, j : Integer) "
	    "         (positive? i => plus(i, j) = succ(plus(pred i, j)))) "
	    "       && (fa(i : Integer, j : Integer) "
	    "            (negative? i => plus(i, j) = pred(plus(succ i, j))))"
	    " "
	    " op  - ((i, j) : Integer * Integer) infixl 25 : Integer = i + - j"
	    " op  * infixl 27 : Integer * Integer -> Integer"
	    " conjecture Integer.*_Obligation_the is "
	    "    ex1(times : Integer * Integer -> Integer) "
	    "     (fa(j : Integer) times(0, j) = 0) "
	    "     && (fa(i : Integer, j_1 : Integer) "
	    "          (positive? i => times(i, j_1) = times(pred i, j_1) + j_1)) "
	    "        && (fa(i_1 : Integer, j_2 : Integer) "
	    "             (negative? i_1 "
	    "             => times(i_1, j_2) = times(succ i_1, j_2) - j_2))"
	    " "
	    " def * = "
	    "   the (times : Integer * Integer -> Integer) "
	    "    (fa(j : Integer) times(zero, j) = zero) "
	    "    && (fa(i : Integer, j : Integer) "
	    "         (positive? i => times(i, j) = times(pred i, j) + j)) "
	    "       && (fa(i : Integer, j : Integer) "
	    "            (negative? i => times(i, j) = times(succ i, j) - j))"
	    " "
	    " op  < ((i, j) : Integer * Integer) infixl 20 : Boolean = negative?(i - j)"
	    " "
	    " op  > ((i, j) : Integer * Integer) infixl 20 : Boolean = j < i"
	    " "
	    " op  <= ((i, j) : Integer * Integer) infixl 20 : Boolean = i < j || i = j"
	    " "
	    " op  >= ((i, j) : Integer * Integer) infixl 20 : Boolean = i > j || i = j"
	    " op  abs : Integer -> {j : Integer | j >= zero}"
	    " conjecture Integer.abs_Obligation_subsort is "
	    "    fa(i : Integer) ~(i >= 0) => - i >= 0"
	    " "
	    " def abs i = if i >= zero then i else - i"
	    " type NonZeroInteger = {i : Integer | i ~= zero}"
	    " "
	    " op  div infixl 26 : Integer * NonZeroInteger -> Integer"
	    " conjecture Integer.div_Obligation_the is "
	    "    fa(j : NonZeroInteger, i : Integer) "
	    "     ex1(q : Integer) "
	    "      (ex(r : Integer) "
	    "        (abs i = abs j * abs q + r && 0 <= r && r < abs j)) "
	    "      && (i * j >= 0 => q >= 0) && (i * j <= 0 => q <= 0)"
	    " "
	    " def div (i, j) = "
	    "   the (q : Integer) "
	    "    (ex(r : Integer) "
	    "      (abs i = abs j * abs q + r && zero <= r && r < abs j)) "
	    "    && (i * j >= zero => q >= zero) && (i * j <= zero => q <= zero)"
	    " "
	    " op  / infixl 26 : Integer * NonZeroInteger -> Integer = div"
	    " "
	    " op  rem ((i, j) : Integer * NonZeroInteger) infixl 26 : Integer = "
	    "   i - j * (i / j)"
	    " "
	    " op  min ((i, j) : Integer * Integer) : Integer = if i < j then i else j"
	    " "
	    " op  max ((i, j) : Integer * Integer) : Integer = if i > j then i else j"
	    " "
	    " op  compare ((i, j) : Integer * Integer) : Compare.Comparison = "
	    "   if i < j then Less else if i > j then Greater else Equal"
	    " "
	    " op  divides ((x, y) : Integer * Integer) infixl 20 : Boolean = "
	    "   ex(z : Integer) x * z = y"
	    " theorem Integer.non_zero_divides_iff_zero_remainder is "
	    "    fa(x : NonZeroInteger, y : Integer) x divides y <=> y rem x = zero"
	    " proof Isa"
	    "    sorry"
	    "  end-proof"
	    " theorem Integer.any_divides_zero is fa(x : Integer) x divides zero"
	    " proof Isa"
	    "    apply(simp add: Integer__divides_def)"
	    "  end-proof"
	    " theorem Integer.only_zero_is_divided_by_zero is "
	    "    fa(x : Integer) zero divides x => x = zero"
	    " proof Isa"
	    "      apply(simp add: Integer__divides_def)"
	    "  end-proof"
	    " "
	    " op  multipleOf ((x, y) : Integer * Integer) infixl 20 : Boolean = y divides x"
	    " op  gcd : Integer * Integer -> {z : Integer | z >= zero}"
	    " conjecture Integer.gcd_Obligation_subsort is "
	    "    fa(y : Integer, x : Integer) "
	    "     (the (z : Integer) "
	    "       z >= 0 "
	    "       && z divides x "
	    "          && z divides y "
	    "             && (fa(w : Integer) (w divides x && w divides y => w divides z))) "
	    "     >= 0"
	    " conjecture Integer.gcd_Obligation_the is "
	    "    fa(y : Integer, x : Integer) "
	    "     ex1(z : Integer) "
	    "      z >= 0 "
	    "      && z divides x "
	    "         && z divides y "
	    "            && (fa(w : Integer) (w divides x && w divides y => w divides z))"
	    " "
	    " def gcd (x, y) = "
	    "   the (z : Integer) "
	    "    z >= zero "
	    "    && z divides x "
	    "       && z divides y "
	    "          && (fa(w : Integer) (w divides x && w divides y => w divides z))"
	    " "
	    " op  lcm : Integer * Integer -> {z : Integer | z >= zero}"
	    " conjecture Integer.lcm_Obligation_subsort is "
	    "    fa(y : Integer, x : Integer) "
	    "     (the (z : Integer) "
	    "       z >= 0 "
	    "       && z multipleOf x "
	    "          && z multipleOf y "
	    "             && (fa(w : Integer) "
	    "                  (w multipleOf x && w multipleOf y => z multipleOf w))) >= 0"
	    " conjecture Integer.lcm_Obligation_the is "
	    "    fa(y : Integer, x : Integer) "
	    "     ex1(z : Integer) "
	    "      z >= 0 "
	    "      && z multipleOf x "
	    "         && z multipleOf y "
	    "            && (fa(w : Integer) "
	    "                 (w multipleOf x && w multipleOf y => z multipleOf w))"
	    " "
	    " def lcm (x, y) = "
	    "   the (z : Integer) "
	    "    z >= zero "
	    "    && z multipleOf x "
	    "       && z multipleOf y "
	    "          && (fa(w : Integer) "
	    "               (w multipleOf x && w multipleOf y => z multipleOf w))"
	    " theorem Integer.gcd_of_not_both_zero is "
	    "    fa(x : Integer, y : Integer) "
	    "     x ~= zero || y ~= zero "
	    "     => gcd(x, y) > zero "
	    "        && gcd(x, y) divides x "
	    "           && gcd(x, y) divides y "
	    "              && (fa(w : Integer) "
	    "                   (w divides x && w divides y => gcd(x, y) >= w))"
	    " proof Isa"
	    "    sorry"
	    "  end-proof"
	    " theorem Integer.gcd_of_zero_zero_is_zero is gcd(zero, zero) = zero"
	    " proof Isa"
	    "    sorry"
	    "  end-proof"
	    " theorem Integer.lcm_smallest_abs_multiple is "
	    "    fa(x : Integer, y : Integer, w : Integer) "
	    "     w multipleOf x && w multipleOf y => lcm(x, y) <= abs w"
	    " proof Isa"
	    "    sorry"
	    "  end-proof"
	    " proof Isa Thy_Morphism Presburger"
	    "   type Integer.Integer -> int"
	    "   Integer.zero         -> 0"
	    "   Integer.one          -> 1"
	    "   IntegerAux.-         -> -"
	    "   Integer.~            -> -"
	    "   Integer.+            -> +     Left 25"
	    "   Integer.-            -> -     Left 25"
	    "   Integer.*            -> *     Left 27"
	    "   Integer.<=           -> \\<le> Left 20"
	    "   Integer.<            -> <     Left 20"
	    "   Integer.>=           -> \\<ge> Left 20"
	    "   Integer.>            -> >     Left 20"
	    "   Integer.div          -> div   Left 26"
	    "   Integer.rem          -> mod   Left 26"
	    "   Integer.min          -> min curried"
	    "   Integer.max          -> max curried"
	    "  end-proof"
	    "endspec"
	    (:optional "")
	    (:optional "")
	    ))
 )
