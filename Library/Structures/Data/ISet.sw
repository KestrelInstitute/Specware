(* Sets as functions to Bool, in a manner similar to /Library/General/Set,
except that here we use "ISet" (for "Isabelle set") in place of "Set" so that it
is compatible with /Library/DataStructs/Sets.sw. *)

ISet qualifying spec

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
    type CPO.ISet           -> set (setToPred, Collect)
    CPO.iSetInter           -> \<inter> Left 70
    CPO.reflexive?          -> refl
    CPO.symmetric?          -> sym
    CPO.antisymmetric?      -> antisym
    CPO.transitive?         -> trans
    CPO.equivalence?        -> equivalence
  end-proof

end-spec
