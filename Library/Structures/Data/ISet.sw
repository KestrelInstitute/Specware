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

  % membership
  op [a] memb? (x:a, s:ISet a) infixl 20 : Bool = s x

  % subset
  (* FIXME: map this to Isabelle's subset in the theory morphism below *)
  op [a] subset? (s1:ISet a, s2:ISet a) : Bool =
    fa (x) s1 x => s2 x

  % set intersection
  op [a] iSetInter (s1:ISet a, s2:ISet a) : ISet a =
    fn x:a -> s1 x && s2 x

  (***
   *** Relations
   ***)

  % A Relation is a set of pairs
  type Relation (a,b) = ISet (a * b)

  % take the cross product of two relations
  op [a1,a2,b1,b2] relCross (R1: Relation (a1,b1), R2: Relation (a2,b2))
    : Relation (a1 * a2, b1 * b2) =
    fn ((a1,b1),(a2,b2)) -> R1 (a1,a2) && R2 (b1,b2)

  % take the cross product of the co-domains of R1 and R2, merging their domains
  op [a,b1,b2] relCross2 (R1: Relation (a,b1), R2: Relation (a,b2))
    : Relation (a, b1 * b2) =
    fn (a,(b1,b2)) -> R1 (a,b1) && R2 (a,b2)


  (***
   *** The Category of Relational Composition
   ***)

  % compose two relations
  op [a,b,c] relCompose (R1: Relation (a,b), R2: Relation (b,c)) : Relation (a,c) =
    fn (a,c) -> ex (b) R1 (a,b) && R2 (b,c)

  % composing a relation with = on the left is the identity
  theorem compose_relation_id_left is [a,b]
    fa (R:Relation (a,b))
      relCompose ((=),R) = R

  % composing a relation with = on the left is the identity
  theorem compose_relation_id_right is [a,b]
    fa (R:Relation (a,b))
      relCompose (R,(=)) = R

  % relational composition is associative
  theorem compose_assoc is [a,b,c,d]
    fa (R1:Relation (a,b),R2:Relation (b,c),R3:Relation (c,d))
      relCompose (relCompose (R1,R2),R3) =
      relCompose (R1,relCompose (R2,R3))

  % invert a relation
  op [a,b] relInvert (R: Relation (a,b)) : Relation (b,a) =
    fn (b,a) -> R (a,b)

  (* FIXME: relInvert is an involution in this category *)


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
      | x::y::l' -> R (x,y) && is_r_chain? R (y::l')

  theorem r_chain_append1 is [a]
    fa (R,l1,l2:List a)
      is_r_chain? R l1 && is_r_chain? R l2
        && (l1 = [] || l2 = [] || R(last l1, head l2)) =>
      is_r_chain? R (l1++l2)

  theorem r_chain_append2 is [a]
    fa (R,l1,l2:List a)
      is_r_chain? R (l1++l2) =>
      is_r_chain? R l1 && is_r_chain? R l2

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
    relCompose (R1,R2) = relCompose (R2,R1)

  (* Any relation commutes with itself *)
  theorem relations_commute_self is [a]
    fa (R:EndoRelation a)
      relations_commute? (R,R)

  % Composing two commuting preorders yields a preorder (the Diamond Lemma)
  theorem compose_commuting_preorders is [a]
    fa (R1,R2: PreOrder a)
      relations_commute? (R1,R2) => preOrder? (relCompose (R1,R2))

  % Composing two commuting equivalences yields an equivalence
  theorem compose_commuting_equivalences is [a]
    fa (R1,R2: Equivalence a)
      relations_commute? (R1,R2) => equivalence? (relCompose (R1,R2))


  (***
   *** EndoRelation as a Functor
   ***)

  % The contravariant functor for EndoRelation
  op [a,b] map_endo (f: a -> b) (R: EndoRelation b) : EndoRelation a =
    fn (a1,a2) -> R (f a1, f a2)

  % The contravariant functor laws for EndoRelation
  theorem map_endo_id is [a]
    fa (R: EndoRelation a) map_endo (fn x -> x) R = R
  theorem map_endo_compose is [a,b,c]
    fa (f:a->b,g:b->c,R)
      map_endo (fn x -> g (f x)) R =
      map_endo f (map_endo g R)

  % map_endo preserves a number of properties
  theorem map_endo_reflexivity is [a,b]
    fa (f:a->b,R)
      reflexive? R => reflexive? (map_endo f R)
  theorem map_endo_symmetry is [a,b]
    fa (f:a->b,R)
      symmetric? R => symmetric? (map_endo f R)
  theorem map_endo_transitivity is [a,b]
    fa (f:a->b,R)
      transitive? R => transitive? (map_endo f R)


  (***
   *** Isabelle Theory Morphism
   ***)

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

proof Isa relCompose [simp] end-proof

proof Isa is_r_chain_p_Obligation_exhaustive
  by (metis list.exhaust)
end-proof

proof Isa r_chain_append1
   apply(induction l1, auto)
   apply(cases l2, auto)
   by (smt ISet__is_r_chain_p.elims(2) ISet__is_r_chain_p.elims(3) append.simps(1) append.simps(2) list.inject)
end-proof

proof Isa r_chain_append2
   apply(induction l1, auto)
   apply (metis ISet__is_r_chain_p.simps(2) ISet__is_r_chain_p.simps(3) append_Cons list.exhaust)
   by (metis ISet__is_r_chain_p.elims(3) ISet__is_r_chain_p.simps(3))
end-proof

proof Isa rt_closure_Obligation_subtype
  sorry
end-proof

proof Isa rst_closure_Obligation_subtype
  sorry
end-proof

proof Isa equivalence_rst_closure
  sorry
end-proof

proof Isa relations_commute_p [simp] end-proof

proof Isa compose_commuting_preorders
  sorry
end-proof

proof Isa compose_commuting_equivalences
  sorry
end-proof

proof Isa map_endo [simp] end-proof

proof Isa map_endo_reflexivity
  by (simp add: ISet__reflexive_p__def)
end-proof

proof Isa map_endo_symmetry
  by (metis ISet__map_endo_def inv_image_def sym_inv_image)
end-proof

proof Isa map_endo_transitivity
  by (metis ISet__map_endo_def inv_image_def trans_inv_image)
end-proof

end-spec
