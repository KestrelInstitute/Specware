% Complete partial orders, useful for defining non-termination. A CPO
% is a partial order (reflexive, transitive, and antisymmetric) such
% that any non-empty directed set S has a supremum, written sup S. A
% directed set is a set such that every pair of elements in the set
% has an upper bound (not necessarily least); i.e., all the elements
% in the set are, in a sense, compatible.

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

  % Anti-Symmetry
  op [a] antisymmetric? (r: EndoRelation a) : Bool =
    fa(x,y) r(x,y) && r(y,x) => x = y

  proof Isa antisymmetric_p__def
    by (auto simp add: antisym_def)
  end-proof

  % Transitivity
  op [a] transitive? (r: EndoRelation a) : Bool =
    fa(x,y,z) r(x,y) && r(y,z) => r(x,z)

  proof Isa transitive_p__def
    by (auto simp add: trans_def)
  end-proof

  % A pre-order is a reflexive-transitive relation
  op preOrder? : [a] EndoRelation a -> Bool =
    iSetInter (reflexive?, transitive?)

  type PreOrder a = { r : EndoRelation a | preOrder? r }

  % A partial order is an antisymmetric pre-order
  op partialOrder? : [a] EndoRelation a -> Bool =
    iSetInter (preOrder?, antisymmetric?)

  type PartialOrder a = { r : EndoRelation a | partialOrder? r }

  % An equivalence is a relfexive-symmetric-transitive relation
  op equivalence? : [a] EndoRelation a -> Bool =
    iSetInter (reflexive?, iSetInter (symmetric?, transitive?))

  proof Isa equivalence_p__def
    by (auto simp add: equiv_def)
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
    antisymmetric?          -> antisym
    transitive?             -> trans
    equivalence?            -> equivalence
  end-proof


  %%
  %% We now define the CPOs
  %%

  % non-emptiness of sets
  op [a] nonempty? (S : ISet a) : Bool = ex (x) S x

  % A directed set is a set such that all pairs of elements have an
  % upper bound (not necessarily least)
  op [a] directed? (r : PartialOrder a) (S : ISet a) : Bool =
    fa (x,y) S x => S y => (ex (z) r (x,z) && r (y,z))

  % Upper bounds
  op [a] upperBound? (r : PartialOrder a) (S : ISet a) (ub : a) : Bool =
    fa (x) S x => r (x, ub)

  % A least upper bound is an upper bound that is least
  op [a] leastUpperBound? (r : PartialOrder a) (S : ISet a) (lub : a) : Bool =
    upperBound? r S lub &&
    (fa (x) upperBound? r S x => r (lub, x))

  % Least upper bounds are unique
  theorem leastUpperBound_unique is [a]
    fa (r,S,lub1,lub2)
      leastUpperBound? r S lub1 =>
      leastUpperBound? r S lub2 =>
      lub1 = lub2

  % A CPO is a PartialOrder along with a supremum operator for
  % non-empty directed sets
  op [a] cpo? (r: PartialOrder a) : Bool =
    fa (S) nonempty? S => directed? r S =>
      (ex (lub) leastUpperBound? r S lub)

  type CPO a = { r : PartialOrder a | cpo? r }

  % A pointed CPO is a CPO where sup can also take empty sets, i.e., a
  % CPO with a least element
  op [a] pointedCpo? (r : PartialOrder a) : Bool =
    fa (S) directed? r S =>
      (ex (lub) leastUpperBound? r S lub)

  type PointedCPO a = { r : PartialOrder a | pointedCpo? r }

  % The supremum operator, for both pointed and non-pointed CPOs
  op [a] supremum (r : PartialOrder a, S : ISet a |
                     directed? r S &&
                     ((cpo? r && nonempty? S) || pointedCpo? r)) : a =
    the (lub) leastUpperBound? r S lub


  %%
  %% Examples of CPOs
  %%

  % Equality is a trivial CPO, where the supremum of a chain is just
  % the first element (since all element in the chain are equal)
  theorem eq_is_cpo is [a] cpo? ((=) : PartialOrder a)

  % Lift a CPO on a to a PointedCPO on Option a, where None is the
  % least element
  op [a] pcpo_option_fun (r: CPO a) : EndoRelation (Option a) =
    fn (x,y) ->
      case (x,y) of
        | (None, _) -> true
        | (Some a, None) -> false
        | (Some a1, Some a2) -> r (a1, a2)
  op [a] pcpo_option (r: CPO a) : PointedCPO (Option a) = pcpo_option_fun r

  % lift a pointed CPO on the codomain type to a function type
  op [a,b] pcpo_fun (r : PointedCPO b) : PointedCPO (a -> b) =
    fn (f1,f2) -> fa (a) r (f1 a, f2 a)


  %%
  %% Building least fixed-points with PointedCPOs
  %%

  % f is monotonic w.r.t. a PartialOrder iff it maps related inputs to related outputs
  op [a,b] monotonic? (r_a : PartialOrder a, r_b : PartialOrder b) (f : a -> b) : Bool =
    fa (a1, a2) r_a (a1, a2) => r_b (f a1, f a2)

  % f is continuous iff it is monotonic and preserves suprema
  % op [a,b] continuous? (r_a : CPO a, r_b : CPO b) (f : a -> b) : Bool =
  %   monotonic? (r_a.rel, r_b.rel) f &&
  %   (fa (seq) f (r_a.sup seq) = r_b.sup (fn i -> f (seq i)))

  % Fixed-points
  op [a] fixedPoint? (f : a -> a) (x:a) : Bool = f x = x

  % Least fixed-points
  op [a] leastFixedPoint? (r : PartialOrder a, f : a -> a) (x:a) : Bool =
    fixedPoint? f x && (fa (y) fixedPoint? f y => r (x, y))

  % Any monotonic function has a least fixed-point
  op [a] leastFP (r: PointedCPO a, f : a -> a | monotonic? (r,r) f) : a =
    the (lub) (leastFixedPoint? (r, f) lub)


  %%
  %% Proofs
  %%

  proof Isa leastUpperBound_unique
    proof -
      assume po : "partialOrder_p r"
      assume lub1_pf : "leastUpperBound_p r S lub1"
      assume lub2_pf : "leastUpperBound_p r S lub2"
      have asym : "antisym r"
        by (insert po, simp add: partialOrder_p_def)
      have ub1 : "upperBound_p r S lub1" by (insert lub1_pf, simp add: leastUpperBound_p_def)
      have ub2 : "upperBound_p r S lub2" by (insert lub2_pf, simp add: leastUpperBound_p_def)
      have r12 : "(lub1, lub2) \<in> r"
        by (insert lub1_pf, insert ub2, simp add: leastUpperBound_p_def)
      have r21 : "(lub2, lub1) \<in> r"
        by (insert lub2_pf, insert ub1, simp add: leastUpperBound_p_def)
      show "lub1 = lub2"
        by (insert r12, insert r21, insert asym, rule antisymD, assumption+)
    qed
  end-proof

  proof Isa supremum_Obligation_the
    proof (rule ex_ex1I)
      assume po : "partialOrder_p r"
      assume dir : "directed_p r S"
      assume disj : "cpo_p r \<and> nonempty_p S \<or> pointedCpo_p r"
      show "\<exists> lub . leastUpperBound_p r S lub"
        apply (insert disj, insert dir)
        by (auto simp add: cpo_p_def pointedCpo_p_def)
      fix lub y
      assume lub_lub : "leastUpperBound_p r S lub"
      assume lub_y : "leastUpperBound_p r S y"
      show "lub = y"
        by (insert po, insert lub_lub, insert lub_y, rule leastUpperBound_unique, auto)
    qed
  end-proof

  proof Isa eq_is_cpo_Obligation_subtype
    apply (auto simp add: partialOrder_p_def preOrder_p_def)
    apply (simp add: refl_onI)
    apply (rule transI, auto)
    apply (rule antisymI, auto)
    done
  end-proof

  proof Isa eq_is_cpo
    apply (auto simp add: cpo_p_def nonempty_p_def, rule exI)
    proof -
      fix S x
      assume Sx : "setToPred S x"
      assume dir : "directed_p {(x, y). x = y} S"
      have Selems : "!! y . setToPred S y ==> x = y"
        by (insert dir, simp add: directed_p_def, erule allE, erule allE, erule mp, simp add: Sx)
      have Seq : "S = { x }"
        by (rule set_eqI, auto simp add: Sx Selems)
      have ub : "upperBound_p {(x, y). x = y} S x"
        by (auto simp add: upperBound_p_def Seq)
      show "leastUpperBound_p {(x, y). x = y} S x"
        by (auto simp add: leastUpperBound_p_def ub upperBound_p_def Seq)
    qed
  end-proof

  proof Isa pcpo_option_Obligation_subtype
    apply (simp add: pointedCpo_p_def, rule allI, rule impI)
    proof -
      fix S
      assume cpo : "cpo_p r"
      assume po : "partialOrder_p r"
      assume dir : "directed_p (pcpo_option_fun r) S"
      have lub_emp : "leastUpperBound_p (pcpo_option_fun r) {} None"
        by (simp add: leastUpperBound_p_def pcpo_option_fun_def upperBound_p_def)
      have lub_none : "leastUpperBound_p (pcpo_option_fun r) {None} None"
        by (simp add: leastUpperBound_p_def pcpo_option_fun_def upperBound_p_def)
      have dir_some : "directed_p r {x . Some x \<in> S}"
        apply (insert dir, auto simp add: directed_p_def)
        apply (erule allE, erule allE)
        proof -
          fix x y
          assume Sx : "setToPred S (Some x)"
          assume Sy : "setToPred S (Some y)"
          assume impl : "setToPred S (Some x) \<and> setToPred S (Some y)
                         --> (\<exists>z. setToPred (pcpo_option_fun r) (Some x, z)
                                \<and> setToPred (pcpo_option_fun r) (Some y, z))"
          have ex_z : "\<exists>z. setToPred (pcpo_option_fun r) (Some x, z)
                            \<and> setToPred (pcpo_option_fun r) (Some y, z)"
            by (insert impl, insert Sx, insert Sy, erule mp, simp)
          obtain a where a_ok: "setToPred r (x,a) \<and> setToPred r (y,a)"
            by (insert ex_z, erule exE, case_tac z, auto simp add: pcpo_option_fun_def)
          show "\<exists> a . setToPred r (x,a) \<and> setToPred r (y,a)"
            by (insert a_ok, rule exI, assumption)
        qed
      have lub_r : "nonempty_p {x . Some x \<in> S} ==>
                       \<exists>x . leastUpperBound_p r {x . Some x \<in> S} x"
        by (insert cpo, insert dir_some, auto simp add: cpo_p_def)
      have lub_r_eq : "!! lub . nonempty_p {x . Some x \<in> S } ==>
                         leastUpperBound_p r {x . Some x \<in> S} lub ==>
                         leastUpperBound_p (pcpo_option_fun r) S (Some lub)"
       proof (auto simp add: leastUpperBound_p_def)
         fix lub x
         assume nonemp : "nonempty_p {x . Some x \<in> S}"
         assume ub_lub : "upperBound_p r {x. setToPred S (Some x)} lub"
         assume lub_lub : "\<forall>x. upperBound_p r {x. setToPred S (Some x)} x --> setToPred r (lub, x)"
         show "upperBound_p (pcpo_option_fun r) S (Some lub)"
           by (insert ub_lub, auto simp add: upperBound_p_def pcpo_option_fun_def, case_tac x, auto)
         assume ub_x : "upperBound_p (pcpo_option_fun r) S x"
         obtain a where some_a_in : "Some a \<in> S"
           by (insert nonemp, auto simp add: nonempty_p_def)
         have r_some_a_x : "setToPred (pcpo_option_fun r) (Some a, x)"
           by (insert some_a_in, insert ub_x, auto simp add: upperBound_p_def)
         obtain y where x_eq_some_y : "x = Some y"
           by (insert r_some_a_x, case_tac x, auto simp add: pcpo_option_fun_def)
         show "setToPred (pcpo_option_fun r) (Some lub, x)"
           by (insert x_eq_some_y ub_x lub_lub, erule allE,
               auto simp add: upperBound_p_def pcpo_option_fun_def)
       qed
      have dj : "S = {} | S = {None} | nonempty_p {x . Some x \<in> S}"
        by (auto simp add: nonempty_p_def, case_tac xa, auto, case_tac x, auto)
      obtain lub where islub : "leastUpperBound_p (pcpo_option_fun r) S lub"
        by (insert dj, insert lub_r, insert lub_r_eq, insert lub_none, insert lub_emp, auto)
      show "\<exists>lub . leastUpperBound_p (pcpo_option_fun r) S lub"
        by (rule exI, rule islub)
    qed
  end-proof

  proof Isa pcpo_option_Obligation_subtype0
    proof (auto simp add: partialOrder_p_def preOrder_p_def)
      assume r_refl : "refl r"
      assume r_trans : "trans r"
      assume r_antisym : "antisym r"
      show "refl (pcpo_option_fun r)"
        by (insert r_refl, rule refl_onI, auto simp add: pcpo_option_fun_def,
            case_tac x, auto simp add: refl_onD)
      show "trans (pcpo_option_fun r)"
        by (insert r_trans, rule transI, auto simp add: pcpo_option_fun_def,
            case_tac x, auto, case_tac y, auto, case_tac z, auto, rule transD, auto)
      show "antisym (pcpo_option_fun r)"
        by (insert r_antisym, rule antisymI, auto simp add: pcpo_option_fun_def,
            case_tac x, auto, case_tac y, auto, case_tac y, auto, rule antisymD, auto)
    qed
  end-proof

end-spec
