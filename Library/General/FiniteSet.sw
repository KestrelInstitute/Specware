(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

FSet qualifying spec

(* The spec `Set' defines a subtype `FiniteSet' for finite sets. In principle,
that subtype could be used in specs and then refined, e.g. in terms of lists, to
obtain an executable implementation. In practice, currently Specware requires
morphisms, which are used to express refinement, to map subtypes to subtypes.

For this reason, we introduce here an "alternative" type for finite sets, called
`FSet', and constrain it to be isomorphic to type `FiniteSet'.  Operations on
`FSet' are defined in terms of the isomorphism and of operations in spec `Set'.

By not equating type `FSet' to any other type (we only constrain it to be
isomorphic to type `FiniteSet'), we leave the possibility open to refine it,
e.g. in terms of lists, using current Specware morphisms. All operations
introduced here can be refined, except the isomorphisms. Users of this spec
should not use the isomorphisms, which are only used here internally to
constrain type `FSet'. *)

import Set

type FSet a

% isomorphisms:

op toFSet : [a] Bijection (FiniteSet a, FSet a)

op fromFSet : [a] FSet a -> FiniteSet a = inverse toFSet

% ------------------------------------------------------------------------------
proof Isa -verbatim
lemma FSet__fromFSet_alt_def:
  "FSet__fromFSet = inv_on (Collect finite) FSet__toFSet"
 apply (cut_tac FSet__toFSet_subtype_constr)
 apply (simp add: FSet__fromFSet_def univ_true bij_ON_UNIV_bij_on)
 apply (erule Function__inverse__stp_simp)
done

lemma FSet__fromFSet_alt_bij: 
  "bij_on  FSet__fromFSet UNIV (Collect finite)"
 apply (cut_tac  FSet__toFSet_subtype_constr)
 apply (simp add: FSet__fromFSet_alt_def univ_true bij_ON_UNIV_bij_on)
 apply (erule bij_on_imp_bij_on_inv)
done

lemma FSet__fromFSet_finite:
  "finite (FSet__fromFSet s)"
  apply (cut_tac FSet__fromFSet_alt_bij)
  apply (auto simp add: bij_on_def defined_on_simp_set)
done

lemma FSet__fromFSet_f_f:
  "finite s \<Longrightarrow>  FSet__fromFSet (FSet__toFSet s) = s"
   apply (simp add: FSet__fromFSet_alt_def)
   apply (rule inv_on_f_f)
   apply (cut_tac FSet__toFSet_subtype_constr,
          auto simp add: bij_ON_def bij_on_def )
done
end-proof
% ------------------------------------------------------------------------------

% operations and subtypes (see spec `Set'):

op [a] in? (x:a, s: FSet a) infixl 20 : Bool = x in? fromFSet s

op [a] nin? (x:a, s: FSet a) infixl 20 : Bool = x nin? fromFSet s

op [a] <= (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 <= fromFSet s2

op [a] < (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 < fromFSet s2

op [a] >= (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 >= fromFSet s2

op [a] > (s1: FSet a, s2: FSet a) infixl 20 : Bool =
  fromFSet s1 > fromFSet s2

op [a] /\ (s1: FSet a, s2: FSet a) infixr 25 : FSet a =
  toFSet (fromFSet s1 /\ fromFSet s2)


op [a] \/ (s1: FSet a, s2: FSet a) infixr 24 : FSet a =
  toFSet (fromFSet s1 \/ fromFSet s2)


op [a] -- (s1: FSet a, s2: FSet a) infixl 25 : FSet a =
  toFSet (fromFSet s1 -- fromFSet s2)


op [a,b] * (s1: FSet a, s2: FSet b) infixl 27 : FSet (a * b) =
  toFSet (fromFSet s1 * fromFSet s2)


op [a] power (s: FSet a) : FSet (FSet a) =
  toFSet (map toFSet (power (fromFSet s)))


op empty : [a] FSet a = toFSet empty

op [a] empty? (s: FSet a) : Bool = empty? (fromFSet s)

op [a] nonEmpty? (s: FSet a) : Bool = nonEmpty? (fromFSet s)

type NonEmptyFSet a = (FSet a | nonEmpty?)

op [a] single (x:a) : FSet a = toFSet (single x)

op [a] single? (s: FSet a) : Bool = single? (fromFSet s)

op [a] onlyMemberOf (x:a, s: FSet a) infixl 20 : Bool =
  x onlyMemberOf (fromFSet s)

type SingletonFSet a = (FSet a | single?)

op [a] theMember (s: SingletonFSet a) : a = theMember (fromFSet s)

op [a] <| (s: FSet a, x:a) infixl 25 : FSet a = toFSet (fromFSet s <| x)


op [a] - (s: FSet a, x:a) infixl 25 : FSet a = toFSet (fromFSet s - x)


op [a,b] map (f: a -> b) (s: FSet a) : FSet b = toFSet (map f (fromFSet s))


op [a,b] FSet.mapPartial (f: a -> Option b) (s: FSet a) : FSet b =
  toFSet (Set.mapPartial f (fromFSet s):FiniteSet(b))


op [a] size (s: FSet a) : Nat = size (fromFSet s)

op [a,b] foldable? (c: b, f: b * a -> b, s: FSet a) : Bool =
  foldable? (c, f, fromFSet s)

op [a,b] fold (c: b, f: b * a -> b, s: FSet a | foldable?(c,f,s)) : b =
  fold (c, f, fromFSet s)


op powerf : [a] FSet a -> FSet (FSet a) = power

% we must strengthen the domain to non-empty sets of sets,
% because in spec `Set' we have `//\\ empty = full':
op [a] //\\ (ss: NonEmptyFSet (FSet a)) : FSet a =
  toFSet (//\\ (map fromFSet (fromFSet ss)))


op [a] \\// (ss: FSet (FSet a)) : FSet a =
  toFSet (\\// (map fromFSet (fromFSet ss)))


op [a] forall? (p: a -> Bool) (s: FSet a) : Bool = fromFSet s <= p

op [a] exists? (p: a -> Bool) (s: FSet a) : Bool =
  nonEmpty? (fromFSet s /\ p)

op [a] exists1? (p: a -> Bool) (s: FSet a) : Bool =
  single? (fromFSet s /\ p)

op [a] filter (p: a -> Bool) (s: FSet a) : FSet a =
  toFSet (fromFSet s /\ p)


% convert list to set:

op [a] List.toSet (l: List a) : FSet a = toFSet (fn x -> x in? l)


% intersection of all sets contained in a list:

op [a] List.//\\ (ls: List1 (FSet a)) : FSet a = //\\ (toSet ls)


% union of all sets contained in a list:

op [a] List.\\// (ls: List (FSet a)) : FSet a = \\// (toSet ls)


% Isabelle pragmas

proof Isa in? -> in_fset? end-proof
proof Isa nin? -> nin_fset? end-proof
proof Isa <= -> <=_fset? end-proof
proof Isa < -> <_fset? end-proof
proof Isa >= -> >=_fset? end-proof
proof Isa > -> >_fset? end-proof

proof Isa e_fsl_bsl_Obligation_subtype
 by (rule finite_Int, simp add: FSet__fromFSet_finite)
end-proof

proof Isa e_bsl_fsl_Obligation_subtype
  by (simp add: finite_Un FSet__fromFSet_finite)
end-proof

proof Isa -- -> --_fs end-proof

proof Isa e_dsh_dsh_Obligation_subtype
 by (rule finite_Diff, simp add: FSet__fromFSet_finite)
end-proof

proof Isa * -> *_fset? end-proof

proof Isa e_ast_Obligation_subtype
 by (rule finite_cartesian_product, simp_all add: FSet__fromFSet_finite)
end-proof

proof Isa power_Obligation_subtype
  by (metis FSet__fromFSet_finite PowD Set_P_unfold rev_finite_subset)
end-proof

proof Isa FSet__power_Obligation_subtype0
   apply (simp add: Set__map__stp_def)
   apply (cut_tac s=s in FSet__fromFSet_finite)
   apply (drule finite_Collect_subsets)
   apply (drule_tac f=FSet__toFSet in finite_image_set)
   apply (rule finite_subset, auto simp add: )
end-proof

proof Isa empty -> empty_fset_p end-proof
proof Isa onlyMemberOf -> onlyMemberOf_fs end-proof
proof Isa <| -> with_fs [simp] end-proof

proof Isa e_lt_bar_Obligation_subtype
 by (simp add: FSet__fromFSet_finite)
end-proof

proof Isa - -> -_fset? end-proof

proof Isa e_dsh_Obligation_subtype
 by (simp add: FSet__fromFSet_finite)
end-proof

proof Isa map_Obligation_subtype
  by (simp add: FSet__fromFSet_finite)
end-proof

proof Isa mapPartial_Obligation_subtype
  apply (cut_tac  s=s and f=f in FSet__map_Obligation_subtype)
  apply (rule_tac f=Some in finite_imageD)
  apply (simp only: Set__mapPartial_def image_def Bex_def, auto)
  apply (rule finite_subset, auto)
end-proof

proof Isa fold_Obligation_subtype
 by (simp add: FSet__foldable_p_def)
end-proof

proof Isa FSet__e_fsl_fsl_bsl_bsl_Obligation_subtype
  by (rule finite_Inter, 
      auto simp add: Set__nonEmpty_p_def ex_in_conv [symmetric] 
                     FSet__fromFSet_finite)
end-proof

proof Isa e_bsl_bsl_fsl_fsl_Obligation_subtype  
 by (rule finite_Union, auto simp add: image_iff FSet__fromFSet_finite)
end-proof

proof Isa filter_Obligation_subtype
 by (rule finite_Int, simp add: FSet__fromFSet_finite)
end-proof

proof Isa List__toSet_Obligation_subtype
 by (simp add: member_def  finite_set)
end-proof

proof Isa List__e_fsl_fsl_bsl_bsl_Obligation_subtype
  apply (simp add:FSet__nonEmpty_p_def List__toSet_def Set__nonEmpty_p_def
                  member_def  FSet__fromFSet_def)
  apply (cut_tac FSet__toFSet_subtype_constr, simp add: univ_true)
  apply (smt FSet__fromFSet_def FSet__fromFSet_f_f List.finite_set set_empty)
end-proof


endspec
