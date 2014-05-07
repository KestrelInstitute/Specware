%% This file is intended to hold a variety of theorems about Lists.
%% We could put it in the Base library, but I'd like to restrict that
%% to things that need special handling by Specware (also I don't want
%% to prove the "stp" versions of all these theorems).

spec

import /Library/Base/List_Executable

  %TODO: Does this already exist somewhere?
  theorem equiLong_self is [a]
    fa(lst : List a) lst equiLong lst

  theorem permutationOf_self is [a]
    fa(lst : List a) lst permutationOf lst

  theorem permutationOf_symmetric is [a]
    fa(x : List a, y : List a) (x permutationOf y) = (y permutationOf x)

  theorem permutationOf_cons_and_cons is [a]
    fa(hd:a, tla : List a, tlb : List a) (hd::tla permutationOf hd::tlb) = (tla permutationOf tlb)

  theorem permutationOf_cons_and_cons_lemma is [a]
    fa(hd:a, other : a, tla : List a, tlb : List a) (other::hd::tla permutationOf hd::tlb) = (other::tla permutationOf tlb)

  theorem permutationOf_append_cons is [a]
    fa(hd:a, tl : List a, x : List a) x++(hd::tl) permutationOf hd::(x++tl)

  theorem permutationOf_append_cons_2 is [a]
    fa(hd:a, tl : List a, x : List a) hd::(x++tl) permutationOf x++(hd::tl)

  theorem permutationOf_transitive is [a]
    fa(x : List a, y : List a, z : List a) (x permutationOf y && y permutationOf z) => x permutationOf z

  theorem permutationOf_append is [a]
    fa(x: List a, y: List a, z: List a) x permutationOf y => (x ++ z permutationOf y ++ z)

  theorem permutationOf_append_2 is [a]
    fa(x: List a, y: List a, z: List a) x permutationOf y => (z ++ x permutationOf z ++ y)

  %% Proofs start here:

  proof Isa permutationOf_append
    sorry
  end-proof

  proof Isa permutationOf_append_2
    sorry
  end-proof

  proof Isa permutationOf_self
    apply(simp add: List__permutationOf__1__obligation_refine_def)
    apply(induct lst )
    apply(simp)
    apply(simp)
  end-proof

  proof Isa permutationOf_transitive
    sorry
  end-proof

  proof Isa permutationOf_cons_and_cons
    apply(auto simp add: List__permutationOf__1__obligation_refine_def)
  end-proof

  proof Isa permutationOf_append_cons
    sorry
  end-proof

  proof Isa permutationOf_append_cons_2
    sorry
  end-proof

  proof Isa permutationOf_cons_and_cons_lemma
    sorry
  end-proof

  proof Isa permutationOf_symmetric
    sorry
  end-proof

end-spec
