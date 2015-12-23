(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

EndoRelation qualifying spec

import Relation


type EndoRelation a = Relation(a,a)

% identity:

op id : [a] EndoRelation a = (=)

% identity over given domain:

op [a] idOver (s: Set a) : EndoRelation a = (fn (x,y) -> x in? s && x = y)


% various properties of endorelations:

op [a] reflexive? (r: EndoRelation a) : Bool = (fa(x) r(x,x))

proof Isa reflexive_p__def
  by (simp add: refl_on_def)
end-proof

type ReflexiveRelation a = (EndoRelation a | reflexive?)

op [a] irreflexive? (r: EndoRelation a) : Bool = (fa(x) ~~r(x,x))

proof Isa irreflexive_p__def
  by (simp add: irrefl_def setToPred_def)
end-proof

type IrreflexiveRelation a = (EndoRelation a | irreflexive?)

op [a] symmetric? (r: EndoRelation a) : Bool = (fa(x,y) r(x,y) => r(y,x))

proof Isa symmetric_p__def
  by (simp add: sym_def)
end-proof

type SymmetricRelation a = (EndoRelation a | symmetric?)

op [a] antisymmetric? (r: EndoRelation a) : Bool =
  fa(x,y) r(x,y) && r(y,x) => x = y

proof Isa antisymmetric_p__def
  by (auto simp add: antisym_def)
end-proof

type AntisymmetricRelation a = (EndoRelation a | antisymmetric?)

op [a] asymmetric? (r: EndoRelation a) : Bool =
  fa(x,y) ~ (r(x,y) && r(y,x))

proof Isa asymmetric_p__def
  by (auto simp add: asym_def)
end-proof

type AsymmetricRelation a = (EndoRelation a | asymmetric?)

op [a] transitive? (r: EndoRelation a) : Bool =
  fa(x,y,z) r(x,y) && r(y,z) => r(x,z)

proof Isa transitive_p__def
  by (auto simp add: trans_def)
end-proof

type TransitiveRelation a = (EndoRelation a | transitive?)

op [a] negativeTransitive? (r: EndoRelation a) : Bool =
  fa(x,y,z) ~~r(x,y) && ~~r(y,z) => ~~r(x,z)

type NegativeTransitiveRelation a = (EndoRelation a | negativeTransitive?)

op [a] trichotomous? (r: EndoRelation a) : Bool =
  % exactly one of `r(x,y)', `r(y,x)', and `x = y' holds:
  fa(x,y) r(x,y) && ~~r(y,x) && x ~= y
     || ~~r(x,y) &&   r(y,x) && x ~= y
     || ~~r(x,y) && ~~r(y,x) && x  = y

type TrichotomousRelation a = (EndoRelation a | trichotomous?)

op equivalence? : [a] EndoRelation a -> Bool =
  reflexive? /\ symmetric? /\ transitive?

proof Isa equivalence_p__def
  by (auto simp add: setToPred_def equiv_def)
end-proof

type Equivalence a = (EndoRelation a | equivalence?)

op partialEquivalence? : [a] EndoRelation a -> Bool =
  symmetric? /\ transitive?

type PartialEquivalence a = (EndoRelation a | partialEquivalence?)

op [a] wellFounded? (r: EndoRelation a) : Bool =
  % each non-empty predicate:
  fa (p: a -> Bool) (ex(y:a) p y) =>
  % has a minimal element w.r.t. the relation:
    (ex(y:a) p y && (fa(x:a) p x => ~ (r(x,y))))

proof Isa wellFounded_p__def
  apply (simp add: wf_eq_minimal  Bex_def, safe)
  apply (drule_tac x="Collect p" in spec, drule mp)
  apply (rule_tac x=y in exI, simp)
  apply (clarsimp, rule_tac x=x in exI, clarsimp)
  apply (drule_tac x="setToPred Q" in spec, drule mp)
  apply (rule_tac x=x in exI, simp_all add: setToPred_def)
  apply (clarsimp, rule_tac x=y in exI, clarsimp)
end-proof

type WellFoundedRelation a = (EndoRelation a | wellFounded?)

% closure operators:

op [a] reflexiveClosure (r: EndoRelation a) : ReflexiveRelation a =
  min (fn rc -> r <= rc && reflexive? rc)

op [a] symmetricClosure (r: EndoRelation a) : SymmetricRelation a =
  min (fn rc -> r <= rc && symmetric? rc)

op [a] transitiveClosure (r: EndoRelation a) : TransitiveRelation a =
  min (fn rc -> r <= rc && transitive? rc)

op [a] equivalenceClosure (r: EndoRelation a) : Equivalence a =
  min (fn rc -> r <= rc && equivalence? rc)



proof Isa reflexiveClosure_Obligation_subtype
  apply (simp add: Set__hasMin_p_def isMinIn_s_def refl_on_def )
  apply (rule_tac x="r^=" in  exI, auto)
end-proof

proof Isa reflexiveClosure_Obligation_subtype0
  by (auto simp add: refl_on_def)
end-proof

proof Isa reflexiveClosure__def
  apply (cut_tac r=r in EndoRelation__reflexiveClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule the1I2, erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def , clarify)
  apply (drule_tac x="r^=" in spec, auto simp add: refl_on_def)
end-proof



proof Isa symmetricClosure_Obligation_subtype
  apply (simp add: Set__hasMin_p_def isMinIn_s_def sym_def )
  apply (rule_tac x="r^s" in  exI, auto)
end-proof

proof Isa symmetricClosure_Obligation_subtype0
  apply (cut_tac r=r in EndoRelation__symmetricClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule the1I2, erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def )
end-proof

proof Isa symmetricClosure__def
  apply (cut_tac r=r in EndoRelation__symmetricClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule the1I2, erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def , clarify)
  apply (drule_tac x="r^s" in spec, auto simp add: sym_def)
end-proof

proof Isa transitiveClosure_Obligation_subtype
  apply (simp add: Set__hasMin_p_def isMinIn_s_def )
  apply (rule_tac x="r^+" in  exI, auto)
  apply (rule_tac r=r and a=a and b=b and P="\<lambda>y. (a,y) \<in> s1" 
         in trancl_induct)
  apply (auto, erule transD, auto)
end-proof

proof Isa transitiveClosure_Obligation_subtype0
  apply (cut_tac r=r in EndoRelation__transitiveClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule the1I2, erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def )
end-proof

proof Isa transitiveClosure__def
  apply (cut_tac r=r in EndoRelation__transitiveClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule the1I2, erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def , clarify)
  apply (drule_tac x="r^+" in spec, drule mp, auto)
  apply (rule_tac r=r and a=a and b=b in trancl_induct)
  apply (auto, erule  transD, auto)
end-proof

proof Isa equivalenceClosure_Obligation_subtype
   apply (simp add: Set__hasMin_p_def isMinIn_s_def equiv_def )
   apply (rule_tac x="r^\<equiv>" in  exI,
          auto simp add: refl_rtrancl trans_rtrancl sym_rtrancl sym_symcl)
   apply (rule_tac r="r^s" and a=a and b=b and P="\<lambda>y. (a,y) \<in> s1" 
         in rtrancl_induct)
   apply (simp_all add: refl_on_def sym_def, erule transD, auto)
end-proof

proof Isa equivalenceClosure_Obligation_subtype0
 apply (cut_tac r=r in EndoRelation__equivalenceClosure_Obligation_subtype)
 apply (simp add: Set__min__def)
 apply (rule the1I2, erule Set__min_Obligation_the)
 apply (simp add: isMinIn_s_def  univ_true)
end-proof

proof Isa equivalenceClosure__def
  apply (cut_tac r=r in EndoRelation__equivalenceClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule the1I2, erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def  equiv_def , clarify)
  apply (drule_tac x="r^\<equiv>" in spec, drule mp,
          auto simp add: refl_rtrancl trans_rtrancl sym_rtrancl sym_symcl)
  apply (rule_tac r="r^s" and a=a and b=b in rtrancl_induct)
  apply (simp_all add: refl_on_def sym_def, erule transD, auto)
end-proof


proof Isa Thy_Morphism 
  EndoRelation.id                      -> Id
  EndoRelation.idOver                  -> Id_on
  EndoRelation.reflexive?              -> refl
  EndoRelation.irreflexive?            -> irrefl
  EndoRelation.symmetric?              -> sym
  EndoRelation.asymmetric?             -> asym
  EndoRelation.antisymmetric?          -> antisym
  EndoRelation.transitive?             -> trans
  EndoRelation.equivalence?            -> equivalence
  EndoRelation.wellFounded?            -> wf
  EndoRelation.reflexiveClosure        -> reflcl 
  EndoRelation.symmetricClosure        -> symcl 
  EndoRelation.transitiveClosure       -> trancl
  EndoRelation.equivalenceClosure      -> equivcl
end-proof

  
endspec
