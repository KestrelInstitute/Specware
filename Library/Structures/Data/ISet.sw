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

  (***
   *** Relations
   ***)

  % A Relation is a set of pairs
  type Relation (a,b) = ISet (a * b)

  % invert a relation
  op [a,b] relInvert (R: Relation (a,b)) : Relation (b,a) =
    fn (b,a) -> R (a,b)

  % compose two relations
  op [a,b,c] relCompose (R1: Relation (a,b), R2: Relation (b,c)) : Relation (a,c) =
    fn (a,c) -> ex (b) R1 (a,b) && R2 (b,c)

  % take the cross product of two relations
  op [a1,a2,b1,b2] relCross (R1: Relation (a1,b1), R2: Relation (a2,b2))
    : Relation (a1 * a2, b1 * b2) =
    fn ((a1,b1),(a2,b2)) -> R1 (a1,a2) && R2 (b1,b2)

  % take the cross product of the co-domains of R1 and R2, merging their domains
  op [a,b1,b2] relCross2 (R1: Relation (a,b1), R2: Relation (a,b2))
    : Relation (a, b1 * b2) =
    fn (a,(b1,b2)) -> R1 (a,b1) && R2 (a,b2)


  (***
   *** EndoRelations
   ***)

  % An EndoRelation is a relation from a type to itself
  type EndoRelation a = Relation (a,a)

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

  % The symmetric closure of a relation
  op [a] sym_closure (R: EndoRelation a) : EndoRelation a =
    fn (x,y) -> R (x,y) || R (y,x)

  % An R-chain is a list whose successive elements are related by R
  op [a] is_r_chain? (R: EndoRelation a) (l: List a) : Bool =
    case l of
      | [] -> true
      | [_] -> true
      | x::y::l' -> R (x,y) && is_r_chain? R (y::l)

  theorem r_chain_append is [a]
    fa (R,l1,l2:List a)
      is_r_chain? R l1 && is_r_chain? R l2 =>
      is_r_chain? R (l1++l2)

  % Take the reflexive-transitive closure of a relation
  op [a] rt_closure (R: EndoRelation a) : PreOrder a =
    fn (x,y) ->
      ex (l) head l = x && last l = y && is_r_chain? R l

  % Take the reflexive-symmetric-transitive closure of a relation
  op [a] rst_closure (R: EndoRelation a) : Equivalence a =
    fn (x,y) ->
      ex (l) head l = x && last l = y && is_r_chain? (sym_closure R) l

  % The reflexive-symmetric-transitive closure of an equivalence is itself
  theorem equivalence_rst_closure is [a]
    fa (R: Equivalence a) rst_closure R = R

  % Whether two relations commute, i.e., any R1-R2 path can be turned into an
  % R2-R1 path and vice-versa
  op [a] relations_commute? (R1: EndoRelation a, R2: EndoRelation a) : Bool =
    fa (x,z)
      (ex (y) R1 (x,y) && R2 (y,z)) <=> (ex (y) R2 (x,y) && R1 (y,z))

  % Composing two commuting equivalences yields an equivalence
  theorem compose_commuting_equivalences is [a]
    fa (R1,R2: Equivalence a)
      relations_commute? (R1,R2) => equivalence? (relCompose (R1,R2))


  % Isabelle morphism to map ISet and its associated operators to the
  % Isabelle set type
  proof Isa Thy_Morphism 
    type ISet.ISet           -> set (setToPred, Collect)
    ISet.iSetInter           -> \<inter> Left 70
    ISet.reflexive?          -> refl
    ISet.symmetric?          -> sym
    ISet.antisymmetric?      -> antisym
    ISet.transitive?         -> trans
    ISet.equivalence?        -> equivalence
  end-proof

end-spec
