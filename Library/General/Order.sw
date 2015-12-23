(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Order qualifying spec

import EndoRelation

%%% Generate stp version of orderSubsumption in case it is useful later
proof Isa -stp-theorems end-proof

% various kinds of orders:

op preOrder? : [a] EndoRelation a -> Bool = reflexive? /\ transitive?

type PreOrder a = (EndoRelation a | preOrder?)

op partialOrder? : [a] EndoRelation a -> Bool = preOrder? /\ antisymmetric?

type PartialOrder a = (EndoRelation a | partialOrder?)

op weakOrder? : [a] EndoRelation a -> Bool =
  reflexive? /\ antisymmetric? /\ negativeTransitive?

type WeakOrder a = (EndoRelation a | weakOrder?)

op [a] linearOrder? (r: EndoRelation a) : Bool =
  partialOrder? r &&
  % the following is sometimes called "totality" in the
  % context of orders, but `total?' is already defined in
  % spec `Relation' with a different meaning
  (fa(x,y) r(x,y) || r(y,x))

type LinearOrder a = (EndoRelation a | linearOrder?)

theorem orderSubsumption is [a]
  linearOrder?  <= (weakOrder?    : EndoRelation a -> Bool) &&
  weakOrder?    <= (partialOrder? : EndoRelation a -> Bool) &&
  partialOrder? <= (preOrder?     : EndoRelation a -> Bool)

proof Isa orderSubsumption__stp
  apply (auto simp: Set__e_lt_eq__stp_def Set_P_unfold )
  apply (auto simp: Order__linearOrder_p__stp_def Order__weakOrder_p__stp_def
                    Order__partialOrder_p__stp_def Order__preOrder_p__stp_def
                    setToPred_def)              
  apply (simp add: EndoRelation__negativeTransitive_p__stp_def setToPred_def, clarify)
  apply (thin_tac "EndoRelation__antisymmetric_p__stp P__a x", 
         thin_tac "EndoRelation__reflexive_p__stp P__a x", 
         drule_tac x=y in spec, drule_tac x=z in spec, simp)
  apply (unfold EndoRelation__transitive_p__stp_def,
         drule_tac x=xa in spec, drule_tac x=z in spec, drule_tac x=y in spec,
         simp)
  apply (clarify, case_tac "xa=y", simp, case_tac "z=y", simp)
  apply (rule classical)
  apply (unfold EndoRelation__antisymmetric_p__stp_def,
         drule_tac x=z in spec, drule_tac x=y in spec, simp)
  apply (unfold EndoRelation__negativeTransitive_p__stp_def setToPred_def,
         drule_tac x=xa in spec, drule_tac x=z in spec, drule_tac x=y in spec,
         simp)
end-proof

proof Isa orderSubsumption
  apply (auto simp: Order__linearOrder_p_def Order__weakOrder_p_def
                    Order__partialOrder_p_def Order__preOrder_p_def
                    setToPred_def)
  apply (simp add: EndoRelation__negativeTransitive_p_def setToPred_def, clarify)
  apply (thin_tac "antisym x", thin_tac "refl x", 
         drule_tac x=y in spec, drule_tac x=z in spec, simp)
  apply (erule notE, erule transD, simp_all)
  apply (simp add: trans_def, clarify)
  apply (case_tac "xa=y", simp, case_tac "z=y", simp)
  apply (rule classical)
  apply (unfold antisym_def, drule_tac x=z in spec, drule_tac x=y in spec, simp)
  apply (unfold EndoRelation__negativeTransitive_p_def setToPred_def,
         drule_tac x=xa in spec, drule_tac x=z in spec, drule_tac x=y in spec,
         simp)
end-proof

% make strict version of predicate over endorelations:

op [a] strict (p: EndoRelation a -> Bool) (r: EndoRelation a) : Bool =
  % `r' satisfies strict version of `p' iff:
  irreflexive? r &&       % `r' is irreflexive and
  p (reflexiveClosure r)  % making `r' reflexive satisfies `p'

op strictPreOrder? : [a] EndoRelation a -> Bool = strict preOrder?

type StrictPreOrder a = (EndoRelation a | strictPreOrder?)

op strictPartialOrder? : [a] EndoRelation a -> Bool = strict partialOrder?

type StrictPartialOrder a = (EndoRelation a | strictPartialOrder?)

op strictWeakOrder? : [a] EndoRelation a -> Bool = strict weakOrder?

type StrictWeakOrder a = (EndoRelation a | strictWeakOrder?)

op strictLinearOrder? : [a] EndoRelation a -> Bool = strict linearOrder?

type StrictLinearOrder a = (EndoRelation a | strictLinearOrder?)

% make reflexive/irreflexive relation irreflexive/reflexive:

op [a] strictify (r: ReflexiveRelation a) : IrreflexiveRelation a = r -- id

op unstrictify : [a] IrreflexiveRelation a -> ReflexiveRelation a =
  inverse strictify

proof Isa unstrictify_Obligation_subtype
  apply (simp add: bij_ON_def inj_on_def surj_on_def Ball_def 
                    Order__strictify_def, safe)
  apply (thin_tac "refl x", simp add: refl_on_def, case_tac "a=b", simp)
  apply (thin_tac "_", simp add: set_eq_iff, 
         drule_tac x=a in spec, drule_tac x=b in  spec, simp)
  apply (thin_tac "refl xa", simp add: refl_on_def, case_tac "a=b", simp)
  apply (thin_tac "_", simp add: set_eq_iff, 
         drule_tac x=a in spec, drule_tac x=b in  spec, simp)
  apply (rule_tac x="x \<union> Id" in exI, auto simp: irrefl_def)end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim

(**************************************************************************)
(* Extensions to Order                                                    *)
(**************************************************************************)

lemma Order__linearOrder_p_le_s [simp]: 
  "Order__linearOrder_p {(x,y). x <=_s y}"
  apply (auto simp: Order__linearOrder_p_def Order__partialOrder_p_def 
                    Order__preOrder_p_def 
                    antisym_def trans_def refl_on_def 
                    e_lt_eq_s_def e_lt_s_def setToPred_def
                   )
  apply (erule String__compare_trans, simp,
         erule String__compare_antisym, simp,
         erule String__compare_linear, simp)
  done
end-proof


endspec
