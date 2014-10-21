% Complete pre-orders (technically, these are omega-complete
% pre-orders), used for defining non-termination. This is a pre-order
% (reflexive and transitive, we do not require asymmetry) such that,
% for any ascending chain
%
% a1 <= a2 <= ...
%
% defined by a function f:nat -> a, there is some element sup f that
% is greater than all f i. We also include the "pointed" condition in
% our definition of CPOs, which requires a least element.

spec

  %%
  %% We start by defining Isabelle's sets. This duplicates some effort
  %% from /Library/General/Order, but that library is not compatible
  %% with, e.g., the libraries in /Library/DataStructures, so the
  %% definitions here are specifically made not to clash with the
  %% latter files.
  %%

  % The type of Isabelle sets
  type ISet a = a -> Bool

  proof Isa -verbatim
    abbreviation setToPred :: "'a set => 'a => bool"
    where "setToPred s x \<equiv> x \<in> s"
  end-proof

  % set intersection
  op [a] iSetInter (s1:ISet a, s2:ISet a) : ISet a =
    fn x:a -> s1 x && s2 x

  % An EndoRelation is a relation from a type to itself
  type EndoRelation a = ISet (a * a)

  % forming the cross product of two relations
  op [a,b] relCross (R1: EndoRelation a, R2: EndoRelation b) : EndoRelation (a * b) =
    fn ((a1,b1),(a2,b2)) -> R1 (a1,a2) && R2 (b1,b2)

  % Reflexivity
  op [a] reflexive? (r: EndoRelation a) : Bool = (fa(x) r(x,x))

  proof Isa reflexive_p__def
    by (simp add: refl_on_def)
  end-proof

  % Symmetry
  op [a] symmetric? (r: EndoRelation a) : Bool = (fa(x,y) r(x,y) => r(y,x))

  proof Isa symmetric_p__def
    by (simp add: sym_def)
  end-proof

  % Transitivity
  op [a] transitive? (r: EndoRelation a) : Bool =
    fa(x,y,z) r(x,y) && r(y,z) => r(x,z)

  proof Isa transitive_p__def
    by (auto simp add: trans_def)
  end-proof

  % A preOrder is a reflexive-transitive relation
  op preOrder? : [a] EndoRelation a -> Bool =
    iSetInter (reflexive?, transitive?)

  type PreOrder a = { r : EndoRelation a | preOrder? r }

  % An equivalence is a relfexive-symmetric-transitive relation
  op equivalence? : [a] EndoRelation a -> Bool =
    iSetInter (reflexive?, iSetInter (symmetric?, transitive?))

  proof Isa equivalence_p__def
    by (auto simp add: setToPred_def equiv_def)
  end-proof

  type Equivalence a = (EndoRelation a | equivalence?)

  % A partial equivalence, or PER, need not be reflexive
  op partialEquivalence? : [a] EndoRelation a -> Bool =
    iSetInter (symmetric?, transitive?)

  type PartialEquivalence a = (EndoRelation a | partialEquivalence?)


  % Isabelle morphism to map ISet and its associated operators to the
  % Isabelle set type
  proof Isa Thy_Morphism 
    type ISet               -> set (setToPred, Collect)
    iSetInter               -> \<inter> Left 70
    reflexive?              -> refl
    symmetric?              -> sym
    transitive?             -> trans
    equivalence?            -> equivalence
  end-proof


  %%
  %% We now define the CPOs
  %%

  % A chain is an ascending sequence
  op [a] chain? (r : PreOrder a) (seq : Nat -> a) : Bool =
    fa (i) r (seq i, seq (i+1))

  % A CPO is a PreOrder along with a supremum operator and a least element
  op [a] cpo? (r : PreOrder a, bot : a, sup : (Nat -> a) -> a) : Bool =
    (fa (seq,i) chain? r seq => r (seq i, sup seq)) &&
    (fa (a) r (bot, a))

  type CPO a = { cpo : (PreOrder a * a * ((Nat -> a) -> a)) | cpo? cpo }


  % FIXME HERE: define some CPOs!

  % lift a preorder to an Option type
  op [a] cpo_option (r_a: PreOrder a) : PreOrder (Option a) =
    fn (x,y) -> fa (a) x = Some a => (ex (a') r_a (a,a') && y = Some a')

  % lift a preorder on the codomain type to a preorder on a function type
  op [a,b] cpo_fun (r_b : PreOrder b) : PreOrder (a -> b) =
    fn (f1,f2) -> fa (a) r_b (f1 a, f2 a)

  % the equivalence relation derived from an ordering
  %op [a] cpo_equiv (r_a: PreOrder a) : Equivalence a =
  %  fn (a1, a2) -> r_a (a1, a2) && r_a (a2, a1)

  % specify that f is monotonic w.r.t. input order r_a and output order r_b
  op [a,b] monotonic? (r_a : PreOrder a, r_b : PreOrder b) (f : a -> b) : Bool =
    fa (a1, a2) r_a (a1, a2) => r_b (f a1, f a2)

end-spec
