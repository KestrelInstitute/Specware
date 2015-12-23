(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Function qualifying spec

(* This spec is an extension of the base spec for functions. *)

import Set

% inversion of an injective function (totalized using Option):

op [a,b] invinj (f: Injection(a,b)) : b -> Option a =
  fn y:b -> if (ex(x:a) f x = y) then Some (the(x:a) f x = y) else None

proof Isa invinj_Obligation_the
 by (auto simp: inj_onD)
end-proof

% we can "invert" a set-valued function that maps distinct domain elements to
% disjoint sets, totalizing it via Option:

op [a,b] invsetfun
         (f: a -> Set b | fa (x1:a, x2:a) x1 ~= x2 => f x1 /\ f x2 = empty)
         : b -> Option a =
  fn y:b -> if (ex(x:a) y in? f x) then Some (the(x:a) y in? f x) else None

proof Isa invsetfun_Obligation_the
 by blast
end-proof

endspec
