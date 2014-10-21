% Complete pre-orders (technically, these are omega-complete
% pre-orders), used for defining non-termination. This is a pre-order
% (reflexive and transitive, we do not require asymmetry) such that
% any ascending chain
%
% a1 <= a2 <= ...
%
% defined by a function f:nat -> a has a least upper bound sup f.

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

  % The base type of a CPO (without the subtype condition)
  type CPO_base a = { rel: PreOrder a, sup: (Nat -> a) -> a }

  % A CPO is a PreOrder along with a supremum operator, where the
  % latter must return an upper bound that is least
  op [a] cpo? (cpo: CPO_base a) : Bool =
    (fa (seq,i) chain? cpo.rel seq => cpo.rel (seq i, cpo.sup seq)) &&
    (fa (seq,a)
       chain? cpo.rel seq => (fa (i) cpo.rel (seq i, a)) =>
       cpo.rel (cpo.sup seq, a))

  type CPO a = { cpo : CPO_base a | cpo? cpo }

  % The base type of a PointedCPO (without the subtype condition)
  type PointedCPO_base a = { cpo: CPO a, bot: a }

  % Helper accessors for PointedCPOs
  op [a] pcpo_rel (pcpo : PointedCPO_base a) : PreOrder a = pcpo.cpo.rel
  op [a] pcpo_sup (pcpo : PointedCPO_base a) : (Nat -> a) -> a = pcpo.cpo.sup

  % A pointed CPO is a CPO with a least element
  op [a] pointedCpo? (pcpo : PointedCPO_base a) : Bool =
    cpo? (pcpo.cpo) && (fa (a) (pcpo.cpo.rel) (pcpo.bot, a))

  type PointedCPO a = { pcpo : PointedCPO_base a | pointedCpo? pcpo }


  %%
  %% Examples of CPOs
  %%

  % Equality is a trivial CPO, where the supremum of a chain is just
  % the first element (since all element in the chain are equal)
  op [a] cpo_eq : CPO a = { rel = (=), sup = (fn seq -> seq 0) }

  % Similarly, any equivalence is a CPO
  op [a] cpo_equ (e : Equivalence a) : CPO a = { rel = e, sup = (fn seq -> seq 0) }

  % Lift a CPO on a to a PointedCPO on Option a, where None is the
  % least element

  op [a] pcpo_option_rel (r: CPO a) : EndoRelation (Option a) =
    fn (x,y) ->
      case (x,y) of
        | (None, _) -> true
        | (Some a, _) -> false
        | (Some a1, Some a2) -> r.rel (a1, a2)
  op [a] pcpo_option_sup (r: CPO a) (seq : Nat -> Option a) : Option a =
    if (fa (i) seq i = None) then None else
      let i0 = the (i) (seq i ~= None && (fa (j) j < i => seq j = None)) in
      Some (r.sup (fn i ->
                   case seq (i+i0) of
                     | None -> the (a) (seq i0 = Some a)
                     | Some a -> a))

  op [a] pcpo_option (r: CPO a) : PointedCPO (Option a) =
    { cpo = { rel = pcpo_option_rel r, sup = pcpo_option_sup r}, bot = None }


  % lift a pointed CPO on the codomain type to a function type
  op [a,b] pcpo_fun (r : PointedCPO b) : PointedCPO (a -> b) =
    {cpo = {rel = (fn (f1,f2) -> fa (a) r.cpo.rel (f1 a, f2 a)),
            sup = (fn seq -> fn a -> r.cpo.sup (fn i -> seq i a))},
     bot = (fn a -> r.bot)}

  % the equivalence relation derived from an ordering
  op [a] preorder_equiv (r_a: PreOrder a) : Equivalence a =
    fn (a1, a2) -> r_a (a1, a2) && r_a (a2, a1)


  %%
  %% Building least fixed-points with PointedCPOs
  %%

  % f is monotonic w.r.t. a PreOrder iff it maps related inputs to related outputs
  op [a,b] monotonic? (r_a : PreOrder a, r_b : PreOrder b) (f : a -> b) : Bool =
    fa (a1, a2) r_a (a1, a2) => r_b (f a1, f a2)

  % f is continuous iff it is monotonic and preserves suprema
  op [a,b] continuous? (r_a : CPO a, r_b : CPO b) (f : a -> b) : Bool =
    monotonic? (r_a.rel, r_b.rel) f &&
    (fa (seq) f (r_a.sup seq) = r_b.sup (fn i -> f (seq i)))

  % f is continuous w.r.t. pointed CPOs iff it also preserves bottom
  op [a,b] pcontinuous? (r_a : PointedCPO a, r_b : PointedCPO b) (f : a -> b) : Bool =
    continuous? (r_a.cpo, r_b.cpo) f && f r_a.bot = r_b.bot

  % The least fixed-point of f, assuming it is pcontinuous, is the
  % supremum of bot, f bot, f (f bot), etc.
  op [a] multiApp (f : a -> a) (i : Nat) (x : a) : a =
    if i = 0 then x else f (multiApp f (i-1) x)
  op [a] leastFP (r: PointedCPO a, f : a -> a | pcontinuous? (r,r) f) : a =
    r.cpo.sup (fn i -> multiApp f i r.bot)

  % Theorem: leastFP is a fixed-point of f
  theorem leastFP_fixed_point is [a]
    fa (r,f) pcontinuous? (r,r) f =>
      preorder_equiv r.cpo.rel (f (leastFP (r,f)), leastFP (r,f))

  % Theorem: leastFP is the least fixed-point of f
  theorem leastFP_least is [a]
    fa (r,f,fp) pcontinuous? (r,r) f =>
      preorder_equiv r.cpo.rel (f fp, fp) =>
      r.cpo.rel (leastFP (r,f), fp)

end-spec
