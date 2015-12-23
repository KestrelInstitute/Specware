(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Relation qualifying spec

import Set

% relations as sets of pairs:

type Relation(a,b) = Set (a * b)

% domain and range:

op [a,b] domain (r: Relation(a,b)) : Set a = fn x:a -> (ex(y:b) r(x,y))

proof Isa domain__def
  by (auto simp add: Domain_iff)
end-proof

op [a,b] range (r: Relation(a,b)) : Set b = fn y:b -> (ex(x:a) r(x,y))

proof Isa range__def
  by (auto simp add: Range_iff)
end-proof

% range/domain values related to domain/range value (set):

op [a,b] apply (r: Relation(a,b)) (x:a) : Set b = fn y:b -> r(x,y)

op [a,b] applyi (r: Relation(a,b)) (y:b) : Set a = fn x:a -> r(x,y)

op [a,b] applys (r: Relation(a,b)) (xS: Set a) : Set b =
  fn y:b -> (ex(x:a) x in? xS && r(x,y))

proof Isa applys__def
  by (simp add: Image_def Bex_def)
end-proof

op [a,b] applyis (r: Relation(a,b)) (yS: Set b) : Set a =
  fn x:a -> (ex(y:b) y in? yS && r(x,y))

% forward and backward composition:

op [a,b,c] :> (r1: Relation(a,b), r2: Relation(b,c)) infixl 24
              : Relation(a,c) = fn (x:a,z:c) -> (ex(y:b) r1(x,y) && r2(y,z))

op [a,b,c] o (r1: Relation(b,c), r2: Relation(a,b)) infixl 24
             : Relation(a,c) = r2 :> r1
proof Isa -> o_R end-proof
% proof Isa [simp] end-proof

% inverse:

op [a,b] inverse (r: Relation(a,b)) : Relation(b,a) = fn (y,x) -> r(x,y)

proof Isa inverse__def
  by (simp add: converse_def)
end-proof

% remove pairs whose domain/range value is not in argument set:

op [a,b] restrictDomain (r: Relation(a,b), xS: Set a) infixl 25
                        : Relation(a,b) = fn (x,y) -> r(x,y) && x in? xS

op [a,b] restrictRange (r: Relation(a,b), yS: Set b) infixl 25
                       : Relation(a,b) = fn (x,y) -> r(x,y) && y in? yS

% some range value for every domain value:

op [a,b] total? (r: Relation(a,b)) : Bool = (domain r = full)

type TotalRelation(a,b) = (Relation(a,b) | total?)

% some domain value for every range value:

op [a,b] surjective? (r: Relation(a,b)) : Bool = (range r = full)

type SurjectiveRelation(a,b) = (Relation(a,b) | surjective?)

% at most one range value for every domain value:

op [a,b] functional? (r: Relation(a,b)) : Bool =
  fa(x) (single? \/ empty?) (apply r x)

type FunctionalRelation(a,b) = (Relation(a,b) | functional?)

% at most one domain value for every range value:

op [a,b] injective? (r: Relation(a,b)) : Bool =
  fa(y) (single? \/ empty?) (applyi r y)

type InjectiveRelation(a,b) = (Relation(a,b) | injective?)

% exactly one range/domain value for each domain/range value:

op [a,b] bijective? : Relation(a,b) -> Bool =
  total? /\ surjective? /\ functional? /\ injective?

type BijectiveRelation(a,b) = (Relation(a,b) | bijective?)

% relative totality, surjectivity, and bijectivity:

op [a,b] totalOn? (s:Set a) (r:Relation(a,b)) : Bool =
  domain r = s

op [a,b] surjectiveOn? (s:Set b) (r:Relation(a,b)) : Bool =
  range r = s

op [a,b] bijectiveOn? (s:Set a) (s':Set b) : Relation(a,b) -> Bool =
  totalOn? s /\ surjectiveOn? s' /\ functional? /\ injective?

% cardinalities:

type      FiniteRelation(a,b) = (Relation(a,b) | finite?)
type    InfiniteRelation(a,b) = (Relation(a,b) | infinite?)
type   CountableRelation(a,b) = (Relation(a,b) | countable?)
type UncountableRelation(a,b) = (Relation(a,b) | uncountable?)

proof Isa Thy_Morphism 
  Relation.domain -> Domain 
  Relation.range  -> Range
  Relation.applys -> Image
  Relation.:> -> O Left 75
  Relation.inverse -> converse
%%  Relation.apply -> 
%%  Relation.applyi -> 
%%  Relation.applyis -> 
%%  Relation.o ->  
%%  Relation.restrictDomain -> 
%%  Relation.restrictRange -> 
%%  Relation.total? -> 
%%  Relation.surjective? -> 
%%  Relation.functional? -> 
%%  Relation.injective? -> 
%%  Relation.bijective? -> 
%%  Relation.totalOn? -> 
%%  Relation.surjectiveOn? -> 
%%  Relation.bijectiveOn? -> 
end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim

(**************************************************************************)
(* Extensions to SW_Relation                                              *)
(**************************************************************************)

lemma Relation__functional_p__stp_alt_def:
  "Relation__functional_p__stp (P,Q) m = 
  (   (\<forall>x \<in> Collect P \<inter> Domain m. \<exists>!y. (x, y) \<in> m)
   \<and> (\<forall>y \<in> Relation__range__stp P m. y \<in> Collect Q))"
 apply (simp add: Relation__functional_p__stp_def Relation__apply_def Bex_def Ball_def
                  Relation__domain__def Relation__range__stp_def,
        simp add: Set__single_p__stp_def,
        auto)
 apply (drule_tac x=x in spec, simp, erule disjE, clarify)
 apply (simp add: set_eq_iff, simp,
        simp only: set_eq_iff)
 apply (drule_tac x=xa in spec, simp)
 apply metis
 done

lemma Relation__functional_p__stp_alt2_def:
    "Relation__functional_p__stp (P,Q) m = 
     ((\<forall>x \<in> Collect P \<inter> Domain m. \<exists>!y. (x, y) \<in> m) \<and> (\<forall>y. (\<exists>x \<in> Collect P. (x, y) \<in> m) \<longrightarrow> y \<in> Collect Q))"
by (simp add: Relation__functional_p__stp_alt_def
              Relation__range__stp_def Ball_def Bex_def)


lemma Relation__injective_p__stp_alt_def:
    "Relation__injective_p__stp (P,Q) m = 
     ((\<forall>y \<in> Collect Q \<inter> Range m. \<exists>!x. (x, y) \<in> m) \<and> (\<forall>x \<in> Relation__domain__stp Q m. x \<in> Collect P))"
 apply (simp add: Relation__injective_p__stp_def Relation__applyi_def 
                  Bex_def Ball_def
                  Relation__range__def Relation__domain__stp_def,
        simp add:  Set__single_p__stp_def,
        auto simp add: )
 apply (drule_tac x=x in spec, simp, erule disjE, clarify)
 apply (simp add: set_eq_iff, simp add: )
 apply (drule_tac x=y in spec, simp, drule mp, erule exI)
 apply (drule_tac x=x in spec, drule mp, rule_tac x=y in exI, simp)
 apply (drule_tac x=x in spec, drule mp, simp)
 apply (simp add: set_eq_iff)
 apply (erule ex1E, auto)
done



lemma Relation__injective_p__stp_alt2_def:
    "Relation__injective_p__stp (P,Q) m = 
     ((\<forall>y \<in> Collect Q \<inter> Range m. \<exists>!x. (x, y) \<in> m) \<and> (\<forall>x. (\<exists>y \<in> Collect Q. (x, y) \<in> m) \<longrightarrow> x \<in> Collect P))"
by (simp add: Relation__injective_p__stp_alt_def
              Relation__domain__stp_def Ball_def Bex_def)

lemma Relation__total_p__stp_alt_def:
    "Relation__total_p__stp (P,Q) m = (\<forall>x \<in> Collect P. x \<in> Relation__domain__stp Q m)"
by (simp add: Relation__total_p__stp_def Ball_def set_eq_iff, auto)

lemma Relation__total_p__stp_alt2_def:
    "Relation__total_p__stp (P,Q) m = (\<forall>x \<in> Collect P. \<exists>y \<in> Collect Q. (x, y) \<in> m)"
by (simp add: Relation__total_p__stp_alt_def
              Relation__domain__stp_def Bex_def)

lemma Relation__surjective_p__stp_alt_def:
    "Relation__surjective_p__stp (P,Q) m = (\<forall>y \<in> Collect Q. y \<in> Relation__range__stp P m)"
by (simp add: Relation__surjective_p__stp_def Ball_def set_eq_iff, auto)

lemma Relation__surjective_p__stp_alt2_def:
    "Relation__surjective_p__stp (P,Q) m = (\<forall>y \<in> Collect Q. \<exists>x \<in> Collect P. (x, y) \<in> m)"
by (simp add: Relation__surjective_p__stp_alt_def
              Relation__range__stp_def Bex_def)

lemma Relation__domain__stp_sub_Domain [simp]:
  "\<lbrakk>x \<in> Relation__domain__stp Q m\<rbrakk> \<Longrightarrow> x \<in> Domain m"
by (auto simp add: Relation__domain__def Relation__domain__stp_def)

(*********************************** Sets are not predicates anymore **********
lemma Relation__domain__stp_sub_Domain1 [simp]:
  "\<lbrakk>Relation__domain__stp Q m x\<rbrakk> \<Longrightarrow> Domain m x"
  by (cut_tac Q=Q in  Relation__domain__stp_sub_Domain, simp_all)
******************************************************************************)
lemma Relation__domain__stp_sub_Domain2 [simp]:
  "Relation__domain__stp Q m \<subseteq> Domain m"
by auto

lemma Relation__range__stp_sub_Range [simp]:
  "\<lbrakk>y \<in> Relation__range__stp P m\<rbrakk> \<Longrightarrow>  y \<in> Range m"
by (auto simp add: Relation__range__def Relation__range__stp_def)

(*********************************** Sets are not predicates anymore **********
lemma Relation__range__stp_sub_Range1 [simp]:
  "\<lbrakk>Relation__range__stp P m y\<rbrakk> \<Longrightarrow>  Range m y"
by (cut_tac P=P in  Relation__range__stp_sub_Range, simp_all)
******************************************************************************)


lemma Relation__range__stp_sub_Range2 [simp]:
  "Relation__range__stp P m \<subseteq> Range m"
by auto

lemma Relation__bijective_p__stp_alt_def:
    "Relation__bijective_p__stp (P,Q) m = 
       (Relation__domain__stp Q m = Collect P \<and> Relation__range__stp P m = Collect Q
       \<and> (\<forall>x \<in> Collect P. \<exists>!y. (x, y) \<in> m) \<and> (\<forall>y \<in> Collect Q. \<exists>!x. (x, y) \<in> m))"
 apply (simp add: Relation__bijective_p__stp_def setToPred_def
                  Relation__domain__stp_def
                  Relation__range__stp_def
                  Relation__injective_p__stp_alt_def
                  Relation__surjective_p__stp_alt_def
                  Relation__total_p__stp_alt_def
                  Relation__functional_p__stp_alt_def
                  Ball_def set_eq_iff Domain_iff Range_iff)
 apply (safe, metis+)
done

lemma Relation__totalOn_p__stp_alt_def:
    "Relation__totalOn_p__stp (P,Q) A m = (Collect P \<inter> Relation__domain__stp Q m = A)"
by (simp add: Relation__totalOn_p__stp_def set_eq_iff)

lemma Relation__surjectiveOn_p__stp_alt_def:
    "Relation__surjectiveOn_p__stp (P,Q) B m = (Collect Q \<inter> Relation__range__stp P m = B)"
by (simp add: Relation__surjectiveOn_p__stp_def set_eq_iff)

lemma Relation__bijectiveOn_p__stp_alt_aux:
    "m \<in> Collect(Relation__bijectiveOn_p__stp (P,Q) A B) = 
       ((Relation__domain__stp Q m = A) \<and> ( Relation__range__stp P m = B)
       \<and> A \<subseteq> Collect P \<and> B \<subseteq> Collect Q 
       \<and> (\<forall>x \<in> Collect P \<inter> Domain m. \<exists>!y. (x, y) \<in> m) \<and> (\<forall>y \<in> Collect Q \<inter> Range m. \<exists>!x. (x, y) \<in> m))"
by (simp add: Relation__bijectiveOn_p__stp_def,
    simp add: Relation__surjectiveOn_p__stp_alt_def
              Relation__totalOn_p__stp_alt_def
              Relation__functional_p__stp_alt_def
              Relation__injective_p__stp_alt_def,
    auto simp add: subset_eq)
 
lemma Relation__bijectiveOn_p__stp_alt_def:
    "Relation__bijectiveOn_p__stp (P,Q) A B m = 
       ((Relation__domain__stp Q m = A) \<and> ( Relation__range__stp P m = B)
       \<and> A \<subseteq> Collect P \<and> B \<subseteq> Collect Q 
       \<and> (\<forall>x \<in> Collect P \<inter> Domain m. \<exists>!y. (x, y) \<in> m) \<and> (\<forall>y \<in> Collect Q \<inter> Range m. \<exists>!x. (x, y) \<in> m))"
by (simp add:  Relation__bijectiveOn_p__stp_alt_aux [symmetric])

(****************************************************************)

lemma unique_singleton1:  (* move this to isabelle Extensions *)
  "(\<exists>x. P = {x}) = (\<exists>!x. x \<in> P)"
  by (auto simp add: set_eq_iff singleton_iff)

(****************************************************************)

lemma Relation__functional_p_alt_def: 
  "Relation__functional_p s = (\<forall>a b c. (a,b) \<in> s \<and> (a,c) \<in> s \<longrightarrow> b=c)"
  apply (auto, simp_all add: Relation__functional_p_def Relation__apply_def,
               simp_all add: unique_singleton1)
  apply (drule_tac x=a in spec, erule disjE)
  apply (erule ex1E, auto simp add: set_eq_iff )
done

lemma Relation__functional_p_empty [simp]:
  "Relation__functional_p {}"
  by (auto simp add: Relation__functional_p_alt_def)

lemma Relation__functional_p_less:
  "Relation__functional_p s \<Longrightarrow> Relation__functional_p (s less (a, b))"
  by (auto simp add: Relation__functional_p_alt_def)

lemma Relation__functional_p_insert:
  "Relation__functional_p (insert (a, b) s) \<Longrightarrow> Relation__functional_p s"
  by (auto simp add: Relation__functional_p_alt_def)

lemma Relation__functional_p_insert_new:
  "\<lbrakk>Relation__functional_p (insert (a, b) s); b \<noteq> c\<rbrakk>  \<Longrightarrow> (a, c) \<notin> s"
  by (auto simp add: Relation__functional_p_alt_def)

(****************************************************************)
lemma Relation__injective_p_alt_def:
 "Relation__injective_p m = 
  (\<forall>y \<in> Range m. \<exists>!x. (x, y) \<in> m)" 
 apply (simp add: Relation__injective_p_def Relation__applyi_def,
        auto simp add: )
 apply(drule_tac x=y in spec, safe)
 apply (simp add: set_eq_iff)
 apply (frule_tac x=xa in spec,drule_tac x=ya in spec,simp)
 apply (simp only: set_eq_iff, simp)
 apply (drule_tac x=y in bspec)
 apply (simp add: Range_def Domain_def, auto)
done
end-proof

endspec
