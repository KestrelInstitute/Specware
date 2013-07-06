% refinement of (finite) sets in terms of (finite) characteristic maps. In fact we maintain the invariant that
% the map is undefined where the element is not in the set. I.e. the set is the domain of the map.  TODO: Why not just use a Map from a to unit, if we don't really ever look at the Bool?
SetsAsMaps =
SetsAsMap qualifying
spec

  import Maps

  type Set a = Map(a, Bool)  %TODO enforce the constraint that all the Bools are true?

% This is imported via Set in Map theory
%TODO The analogue of axiom membership is not provable without the constraint that all Bools are true.
  op [a] in? (x:a, s:Set a) infixl 20 : Bool = (apply s x = Some true)

  % set containment just amounts to map containment, because there are no
  % repeated elements

  op [a] subset (s1: Set a, s2: Set a) infixl 20 : Bool =
    Map.size s1 <= Map.size s2 %drop this? (only okay because of the invariant of all Bools being true)
      && foldi (fn (x, _, val) -> val && x in? s2) true s1

  op [a] empty_set : Set a = empty_map

  op [a] set_insert (x:a, s: Set a) : Set a = update s x true

  %% Not useful for this representation
  op [a] set_insert_new(x:a, s: Set a) : Set a = update s x true

  % To take the union of two sets, we use a map fold, starting with
  % the first map, to go through the second map and insert its
  % elements into the first (using set_insert just defined).
  op [a] \/ (s1: Set a, s2: Set a) infixl 300 : Set a =
    foldi (fn (x,_,result) -> set_insert(x, result))
          s1
          s2

  op [a] /\ (s1: Set a, s2: Set a) infixl 300 : Set a = 
    foldi (fn(x,_,result) -> if x in? s1 then set_insert(x,result) else result)
          empty_set
          s2

  % set_fold amounts to map_fold on the representing map
  op [a,b] set_fold (c:b)
                    (f : b * a -> b |
                         (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                         (fa(x,y)   f(f(x,y), y) = f(x,y)) %TODO drop this, if we redo set fold to not require this?
                         )
                    (s: Set a) : b = 
    foldi (fn (x, _, result) -> f (result, x))
          c 
          s

  %% TTODO This seems wrong.  This starts with the empty set and
  %% intersects more sets into it.  The result will always be empty!
  %% Also, it's not clear what this should return if called on the
  %% empty set (in some sense, the intersection of no sets is the set
  %% containing everything, but these are finite sets). Probably this
  %% should require its argument to be a non-empty set of sets.
  op [a] //\\ (ss:Set (Set a)) : Set a =
    set_fold empty_set (/\) ss

  op [a] \\// (ss:Set (Set a)) : Set a =
    set_fold empty_set (\/) ss

  op [a] set_delete (x:a, s:Set a) : Set a = remove s x

  op [a] -- (s1: Set a, s2: Set a) infixl 25 : Set a =
    foldi (fn (x, _, result) -> remove result x)
          s1
          s2

  %TODO drop this since we have -- ?
  op [a] set_difference (s1: Set a, s2: Set a) : Set a = (s1 -- s2)  % map_difference(s1,s2)

  op [a] size (s: Set a): Nat = Map.size s

  op [a] filter (p: a -> Bool) (s: Set a) : Set a =
     foldi (fn (x,_,result) -> if p x then set_insert(x, result) else result)
           empty_set
           s

  op [a,b] map (f: a -> b) (s: Set a) : Set b =
    foldi (fn (x,_,result) -> set_insert(f x, result))
          empty_set
          s

  % Changed to match the change in Sets.sw -Eric
  op [a] nt_subset (As:Set a, Bs:Set a): Bool =
    if As = empty_set
       then Bs = empty_set  %empty?(Bs)
       else As subset Bs

  op [a] forall? (p: a -> Bool) (s: Set a) : Bool = set_fold true (&&) (map p s)

proof Isa SetsAsMap__e_fsl_fsl_bsl_bsl_Obligation_subtype
  sorry
end-proof

proof Isa SetsAsMap__e_bsl_bsl_fsl_fsl_Obligation_subtype
  sorry
end-proof

end-spec



M = morphism Sets -> SetsAsMaps {Set._ +-> SetsAsMap._}

proof Isa Set__membership
  sorry
end-proof

proof Isa Set__subset_def
  sorry
end-proof

proof Isa Set__empty_set
  apply(simp add: SetsAsMap__empty_set_def SetsAsMap__in_p_def Map__empty_map)
end-proof

proof Isa Set__set_insertion
  apply(simp add: SetsAsMap__set_insert_def SetsAsMap__in_p_def Map__update)
end-proof

proof Isa Set__set_union
  sorry
end-proof

proof Isa Set__set_intersection
  sorry
end-proof

proof Isa Set__induction
  sorry
end-proof

proof Isa Set__set_fold1
  sorry
end-proof

proof Isa Set__set_fold2
  sorry
end-proof

proof Isa Set__set_deletion
  sorry
end-proof

proof Isa Set__set_difference
  sorry
end-proof

proof Isa Set__filter_def
  sorry
end-proof

proof Isa Set__map_def
  sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_def_Obligation_subtype
  sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_def
  sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_def_Obligation_subtype
  sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_def
  sorry
end-proof

proof Isa set_insert_new_def
  sorry
end-proof
