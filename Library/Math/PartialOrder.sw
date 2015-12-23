(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Carrier = spec type A end-spec

PartialOrder = spec

 import Carrier

 op <= infixl 20 : A * A -> Bool

 axiom reflexive_le is
    fa(a:A) a<=a

 axiom transitive_le is
    fa(a:A,b:A,c:A)(a<=b && b<=c => a<=c)

 axiom antisymmetric_le is
    fa(a:A,b:A)(a<=b && b<=a => a=b)

end-spec

MonotoneFn = spec
  import PartialOrder

 op monotone: (A->A) -> Bool
 axiom def_of_monotone is
   fa(f:A->A) ((monotone f) = (fa(a1:A,a2:A) (a1<=a2 => f(a1)<=f(a2))))

end-spec
