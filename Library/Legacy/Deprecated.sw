spec

(* This spec collects deprecated types and ops of the Specware base library. It
will be eventually eliminated. *)

import String

op Function.wfo: [a] (a * a -> Bool) -> Bool

op Option.some : [a] a -> Option a = embed Some
op Option.none : [a]      Option a = embed None

type Integer.NonZeroInteger = Int0

op Nat.natural? (i:Int) : Bool = i >= 0

op Integer.~ : Bijection (Int, Int) = -
proof Isa e_tld_subtype_constr
 apply(rule IntegerAux__e_dsh_subtype_constr)
end-proof

op Integer.rem infixl 26 : Int * Int0 -> Int = modT

theorem Integer.non_zero_divides_iff_zero_remainder is
  fa (x:Int0, y:Int) x divides y <=> y rem x = zero
proof Isa
  apply (simp add: divides_iff_modT_0)
end-proof

proof Isa Thy_Morphism
 type Integer.Integer -> int
 Integer.~            -> -
 Integer.rem          -> modT Left 22
end-proof

endspec
