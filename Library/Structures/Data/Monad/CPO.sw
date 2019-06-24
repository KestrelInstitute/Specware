(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Complete partial orders, useful for defining non-termination. A CPO
% is a partial order (reflexive, transitive, and antisymmetric) such
% that any non-empty directed set S has a supremum, written sup S. A
% directed set is a set such that every pair of elements in the set
% has an upper bound (not necessarily least); i.e., all the elements
% in the set are, in a sense, compatible.

CPO qualifying spec
  import ../ISet

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
      assume po : "ISet__partialOrder_p r"
      assume lub1_pf : "CPO__leastUpperBound_p r S lub1"
      assume lub2_pf : "CPO__leastUpperBound_p r S lub2"
      have asym : "antisym r"
        by (insert po, simp add: ISet__partialOrder_p_def)
      have ub1 : "CPO__upperBound_p r S lub1" by (insert lub1_pf, simp add: CPO__leastUpperBound_p_def)
      have ub2 : "CPO__upperBound_p r S lub2" by (insert lub2_pf, simp add: CPO__leastUpperBound_p_def)
      have r12 : "(lub1, lub2) \<in> r"
        by (insert lub1_pf, insert ub2, simp add: CPO__leastUpperBound_p_def)
      have r21 : "(lub2, lub1) \<in> r"
        by (insert lub2_pf, insert ub1, simp add: CPO__leastUpperBound_p_def)
      show "lub1 = lub2"
        by (insert r12, insert r21, insert asym, rule antisymD, assumption+)
    qed
  end-proof

  proof Isa supremum_Obligation_the
    proof (rule ex_ex1I)
      assume po : "ISet__partialOrder_p r"
      assume dir : "CPO__directed_p r S"
      assume disj : "CPO__cpo_p r \<and> CPO__nonempty_p S \<or> CPO__pointedCpo_p r"
      show "\<exists> lub . CPO__leastUpperBound_p r S lub"
        apply (insert disj, insert dir)
        by (auto simp add: CPO__cpo_p_def CPO__pointedCpo_p_def)
      fix lub y
      assume lub_lub : "CPO__leastUpperBound_p r S lub"
      assume lub_y : "CPO__leastUpperBound_p r S y"
      show "lub = y"
        by (insert po, insert lub_lub, insert lub_y, rule CPO__leastUpperBound_unique, auto)
    qed
  end-proof

  proof Isa eq_is_cpo_Obligation_subtype
    apply (auto simp add: ISet__partialOrder_p_def ISet__preOrder_p_def)
    apply (simp add: refl_onI)
    apply (rule transI, auto)
  end-proof

  proof Isa eq_is_cpo
    apply (auto simp add: CPO__cpo_p_def CPO__nonempty_p_def, rule exI)
    proof -
      fix S x
      assume Sx : "setToPred S x"
      assume dir : "CPO__directed_p {(x, y). x = y} S"
      have Selems : "!! y . setToPred S y ==> x = y"
        by (insert dir, simp add: CPO__directed_p_def, erule allE, erule allE, erule mp, simp add: Sx)
      have Seq : "S = { x }"
        by (rule set_eqI, auto simp add: Sx Selems)
      have ub : "CPO__upperBound_p {(x, y). x = y} S x"
        by (auto simp add: CPO__upperBound_p_def Seq)
      show "CPO__leastUpperBound_p {(x, y). x = y} S x"
        by (auto simp add: CPO__leastUpperBound_p_def ub CPO__upperBound_p_def Seq)
    qed
  end-proof

  proof Isa pcpo_option_Obligation_subtype
    apply (simp add: CPO__pointedCpo_p_def, rule allI, rule impI)
    proof -
      fix S
      assume cpo : "CPO__cpo_p r"
      assume po : "ISet__partialOrder_p r"
      assume dir : "CPO__directed_p (CPO__pcpo_option_fun r) S"
      have lub_emp : "CPO__leastUpperBound_p (CPO__pcpo_option_fun r) {} None"
        by (simp add: CPO__leastUpperBound_p_def CPO__pcpo_option_fun_def CPO__upperBound_p_def)
      have lub_none : "CPO__leastUpperBound_p (CPO__pcpo_option_fun r) {None} None"
        by (simp add: CPO__leastUpperBound_p_def CPO__pcpo_option_fun_def CPO__upperBound_p_def)
      have dir_some : "CPO__directed_p r {x . Some x \<in> S}"
        apply (insert dir, auto simp add: CPO__directed_p_def)
        apply (erule allE, erule allE)
        proof -
          fix x y
          assume Sx : "setToPred S (Some x)"
          assume Sy : "setToPred S (Some y)"
          assume impl : "setToPred S (Some x) \<and> setToPred S (Some y)
                         --> (\<exists>z. setToPred (CPO__pcpo_option_fun r) (Some x, z)
                                \<and> setToPred (CPO__pcpo_option_fun r) (Some y, z))"
          have ex_z : "\<exists>z. setToPred (CPO__pcpo_option_fun r) (Some x, z)
                            \<and> setToPred (CPO__pcpo_option_fun r) (Some y, z)"
            by (insert impl, insert Sx, insert Sy, erule mp, simp)
          obtain a where a_ok: "setToPred r (x,a) \<and> setToPred r (y,a)"
            by (insert ex_z, erule exE, case_tac z, auto simp add: CPO__pcpo_option_fun_def)
          show "\<exists> a . setToPred r (x,a) \<and> setToPred r (y,a)"
            by (insert a_ok, rule exI, assumption)
        qed
      have lub_r : "CPO__nonempty_p {x . Some x \<in> S} ==>
                       \<exists>x . CPO__leastUpperBound_p r {x . Some x \<in> S} x"
        by (insert cpo, insert dir_some, auto simp add: CPO__cpo_p_def)
      have lub_r_eq : "!! lub . CPO__nonempty_p {x . Some x \<in> S } ==>
                         CPO__leastUpperBound_p r {x . Some x \<in> S} lub ==>
                         CPO__leastUpperBound_p (CPO__pcpo_option_fun r) S (Some lub)"
       proof (auto simp add: CPO__leastUpperBound_p_def)
         fix lub x
         assume nonemp : "CPO__nonempty_p {x . Some x \<in> S}"
         assume ub_lub : "CPO__upperBound_p r {x. setToPred S (Some x)} lub"
         assume lub_lub : "\<forall>x. CPO__upperBound_p r {x. setToPred S (Some x)} x --> setToPred r (lub, x)"
         show "CPO__upperBound_p (CPO__pcpo_option_fun r) S (Some lub)"
           by (insert ub_lub, auto simp add: CPO__upperBound_p_def CPO__pcpo_option_fun_def, case_tac x, auto)
         assume ub_x : "CPO__upperBound_p (CPO__pcpo_option_fun r) S x"
         obtain a where some_a_in : "Some a \<in> S"
           by (insert nonemp, auto simp add: CPO__nonempty_p_def)
         have r_some_a_x : "setToPred (CPO__pcpo_option_fun r) (Some a, x)"
           by (insert some_a_in, insert ub_x, auto simp add: CPO__upperBound_p_def)
         obtain y where x_eq_some_y : "x = Some y"
           by (insert r_some_a_x, case_tac x, auto simp add: CPO__pcpo_option_fun_def)
         show "setToPred (CPO__pcpo_option_fun r) (Some lub, x)"
           by (insert x_eq_some_y ub_x lub_lub, erule allE,
               auto simp add: CPO__upperBound_p_def CPO__pcpo_option_fun_def)
       qed
      have dj : "S = {} | S = {None} | CPO__nonempty_p {x . Some x \<in> S}"
        by (auto simp add: CPO__nonempty_p_def, case_tac xa, auto, case_tac x, auto)
      obtain lub where islub : "CPO__leastUpperBound_p (CPO__pcpo_option_fun r) S lub"
        by (insert dj, insert lub_r, insert lub_r_eq, insert lub_none, insert lub_emp, auto)
      show "\<exists>lub . CPO__leastUpperBound_p (CPO__pcpo_option_fun r) S lub"
        by (rule exI, rule islub)
    qed
  end-proof

  proof Isa pcpo_option_Obligation_subtype0
    proof (auto simp add: ISet__partialOrder_p_def ISet__preOrder_p_def)
      assume r_refl : "refl r"
      assume r_trans : "trans r"
      assume r_antisym : "antisym r"
      show "refl (CPO__pcpo_option_fun r)"
        by (insert r_refl, rule refl_onI, auto simp add: CPO__pcpo_option_fun_def,
            case_tac x, auto simp add: refl_onD)
      show "trans (CPO__pcpo_option_fun r)"
        by (insert r_trans, rule transI, auto simp add: CPO__pcpo_option_fun_def,
            case_tac x, auto, case_tac y, auto, case_tac z, auto, rule transD, auto)
      show "antisym (CPO__pcpo_option_fun r)"
        by (insert r_antisym, rule antisymI, auto simp add: CPO__pcpo_option_fun_def,
            case_tac x, auto, case_tac y, auto, case_tac y, auto, rule antisymD, auto)
    qed
  end-proof

  proof Isa pcpo_fun_Obligation_subtype
    proof (simp add: CPO__pointedCpo_p_def, rule allI, rule impI)
      fix S
      assume lub_r : "\<forall>S. CPO__directed_p r S --> (\<exists>lub. CPO__leastUpperBound_p r S lub)"
      assume po_r : "ISet__partialOrder_p r"
      assume dir : "CPO__directed_p {(f1, f2). \<forall>a. setToPred r (f1 a, f2 a)} S"
      define lub where "lub = \<lambda>a . The (CPO__leastUpperBound_p r { f a | f . setToPred S f })"
      have ex_lub_a : "!!a . \<exists>lub_a . CPO__leastUpperBound_p r { f a | f . setToPred S f } lub_a"
        proof (insert lub_r dir, erule allE, erule mp, auto simp add: CPO__directed_p_def)
          fix a f fa
          assume a1 : "\<forall> x y . setToPred S x \<and> setToPred S y -->
                         (\<exists>z. (\<forall>a. setToPred r (x a, z a))
                            \<and> (\<forall>a. setToPred r (y a, z a)))"
          assume a2 : "setToPred S f"
          assume a3 : "setToPred S fa"
          obtain zf where zf_pf : "(\<forall>a. setToPred r (f a, zf a)) \<and> (\<forall>a. setToPred r (fa a, zf a))"
            by (insert a1 a2 a3, erule allE[of _ f], erule allE[of _ fa], erule impE, auto)
          show "\<exists>z. setToPred r (f a, z) \<and> setToPred r (fa a, z)"
            by (insert zf_pf, auto)
        qed
      have lub_a : "\<forall>a . CPO__leastUpperBound_p r { f a | f . setToPred S f } (lub a)"
        proof (rule allI)
          fix a
          obtain lub_a where lub_a_lub : "CPO__leastUpperBound_p r { f a | f . setToPred S f } lub_a"
            by (insert ex_lub_a, auto)
          show "CPO__leastUpperBound_p r {f a |f. setToPred S f} (lub a)"
            by (insert lub_a_lub po_r, simp add: lub_def ISet__partialOrder_p_def,
                rule theI, auto, rule antisymD, assumption,
                auto simp add: CPO__leastUpperBound_p_def)
        qed
      have lub_lub : "CPO__leastUpperBound_p {(f1, f2). \<forall>a. setToPred r (f1 a, f2 a)} S lub"
        by (insert lub_a, auto simp add: CPO__leastUpperBound_p_def CPO__upperBound_p_def, metis)
      show "\<exists> lub . CPO__leastUpperBound_p {(f1, f2). \<forall>a. setToPred r (f1 a, f2 a)} S lub"
        by (rule exI, rule lub_lub)
    qed
  end-proof

  proof Isa pcpo_fun_Obligation_subtype0
    proof (auto simp add: ISet__partialOrder_p_def ISet__preOrder_p_def)
      assume r_refl : "refl r"
      assume r_trans : "trans r"
      assume r_antisym : "antisym r"
      show "refl {(f1, f2). \<forall>a. setToPred r (f1 a, f2 a)}"
        by (insert r_refl, rule refl_onI, auto simp add: refl_onD)
      show "transP (\<lambda>f1 f2. \<forall>a. setToPred r (f1 a, f2 a))"
        by (insert r_trans, rule transI, auto, (erule allE)+, rule transD)
      show "antisymP (\<lambda>f1 f2. \<forall>a. setToPred r (f1 a, f2 a))"
        by (insert r_antisym, rule antisymI, auto simp add: antisymD)
    qed
  end-proof

  % FIXME HERE: prove this by introducing an inductive predicate for
  % the "f-reachable" elements of type a including all elements
  % reachable from bottom using zero or more applications of f and/or
  % supremum. The supremum of this set must be a fixed-point of f.
  proof Isa leastFP_Obligation_the
    sorry
  end-proof

end-spec
