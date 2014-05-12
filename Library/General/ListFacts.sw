%% This file is intended to hold a variety of theorems about Lists.
%% We could put it in the Base library, but I'd like to restrict that
%% to things that need special handling by Specware (also I don't want
%% to prove the "stp" versions of all these theorems).

spec

import /Library/Base/List_Executable

theorem in_l_not_in_delete1_eq is [a]
  fa (x:a, y, l) x in? l => ~(x in? (delete1 (y, l))) => x = y

%TODO: Does this already exist somewhere?
  theorem equiLong_self is [a]
    fa(lst : List a) lst equiLong lst

%TODO: rename theorems too:
theorem permutesTo?_reflexive is [a]
  fa(lst : List a) permutesTo?(lst,lst)

theorem permutesTo?_symmetric is [a]
  fa(x : List a, y : List a) permutesTo?(x,y) = permutesTo?(y,x)

theorem permutesTo?_cons_and_cons is [a]
  fa(hd:a, tla : List a, tlb : List a) permutesTo?(hd::tla,hd::tlb) = permutesTo?(tla,tlb)

theorem permutesTo?_cons_and_cons_lemma is [a]
  fa(hd:a, other : a, tla : List a, tlb : List a) permutesTo?(other::hd::tla, hd::tlb) = permutesTo?(other::tla, tlb)

theorem permutesTo?_append_cons is [a]
  fa(hd:a, tl : List a, x : List a) permutesTo?(x++(hd::tl), hd::(x++tl))

theorem permutesTo?_append_cons_2 is [a]
  fa(hd:a, tl : List a, x : List a) permutesTo?(hd::(x++tl), x++(hd::tl))

theorem permutesTo?_transitive is [a]
  fa(x : List a, y : List a, z : List a) (permutesTo?(x,y) && permutesTo?(y,z)) => permutesTo?(x,z)

theorem permutesTo?_append is [a]
  fa(x: List a, y: List a, z: List a) permutesTo?(x,y) => permutesTo?(x ++ z, y ++ z)

theorem permutesTo?_append_2 is [a]
  fa(x: List a, y: List a, z: List a) permutesTo?(x, y) => permutesTo?(z ++ x, z ++ y)

%% Proofs start here:

proof Isa permutesTo?_append
  sorry
end-proof

proof Isa permutesTo?_append_2
  sorry
end-proof

proof Isa permutesTo?_reflexive
  apply(metis List__permutesTo_p_equiv)
end-proof

proof Isa permutesTo?_transitive
  sorry
end-proof

proof Isa permutesTo?_cons_and_cons
  apply(simp add: List__permutesTo_p_def)
end-proof

proof Isa permutesTo?_append_cons
  apply(simp add: List__permutesTo_p_def)
  apply (metis perm_append_Cons perm_sym)
end-proof

proof Isa permutesTo?_append_cons_2
  apply(simp add: List__permutesTo_p_def)
  apply (metis perm_append_Cons perm_sym)
end-proof

proof Isa permutesTo?_cons_and_cons_lemma
  apply(simp add: List__permutesTo_p_def)
  apply(metis cons_perm_eq perm.swap perm.trans)
end-proof

proof Isa permutesTo?_symmetric
  apply(metis List__permutesTo_p_equiv)
end-proof

proof Isa in_l_not_in_delete1_eq
   apply(metis List__delete1_delete1_curried in_set_remove1)
end-proof

end-spec
