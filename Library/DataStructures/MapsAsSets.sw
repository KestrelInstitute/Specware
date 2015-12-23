(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% refinement of (finite) maps in terms of (finite) sets
MapsAsSets = Map qualifying
spec

  % we refine maps by means of sets: a map can be represented by a set of
  % pairs of type (a,b) such that no two pairs in the set have the same first
  % component but different second components (this is essentially the usual
  % set-theoretic definition)

  % clearly, there exist other ways to refine maps

  % first, we import sets

  import Sets

  % a map is a set of pairs (i.e., a binary relation) satisfying the
  % "functional requirement" (i.e., no element is mapped to different
  % elements)

  op [a,b] no_duplicate_keys? (s : Set(a * b)) : Bool =
    fa(x:a, y1:b, y2:b) (x,y1) in? s && (x,y2) in? s => y1 = y2

  type Map(a,b) = (Set(a * b) | no_duplicate_keys?)

  % we (re-)define the operations on maps to operate on the
  % sets just defined and to be constructive

  % apply is defined by going through the set (by means of set_fold),
  % and looking for a pair whose first component is the given argument:
  % if one is found, the second component is returned (wrapped with
  % Some); if not, None is returned
  %% TODO: I guess this doesn't type check (because the fn isn't foldable over all sets, only over m); we need to change set_fold to require foldability only over the given set.
  op [a,b] apply (m: Map(a,b)) (x:a) : Option b = 
    set_fold None
             (fn (result, (x1,y1)) -> if x = x1 then Some y1 else result)
             m

  %% Will be needed for the morphism and now possibly needed for a proof below:
  theorem map_equality is [a,b]
    fa(m1:Map(a,b), m2:Map(a,b)) (fa(x) apply m1 x = apply m2 x) => m1 = m2

  theorem not_in?_when_apply_is_None is [a,b]
    fa(m:Map(a,b),x:a,val:b)
      ((apply m x) = None) => ~((x,val) in? m)

  %% TODO: I guess this doesn't type check (because the fn isn't foldable over all sets, only over m); we could change set_fold to require foldability only over the given set (or change the fn?).
  op [a,b] map_apply (m : Map(a,b)) (b_default : b) (x : a) : b =
    set_fold b_default
             (fn (result, (x1,y1)) -> if x = x1 then y1 else result)
             m

  % the empty map is represented by the empty set of pairs
  op [a,b] empty_map : Map(a,b) = empty_set

  % there are two cases for updating a map: if a pair with the given
  % first component does not belong to the map, a suitable pair is inserted
  % into the set; otherwise, we go though the set (by means of set_fold)
  % reconstructing it the way it was, except for the pair with the given
  % first component

  op [a,b] update (m: Map(a,b)) (x:a) (y:b) : Map(a,b) =
    if (apply m x = None) then
      set_insert((x,y),m)
    else
      set_fold empty_map
               (fn (result_map: Map(a,b), ((x1,y1) : {(x1,y1) : a*b | ~(x1 in? (domain result_map))})) ->  %%%(result_map,(x1,y1)) ->
                 if x1 = x then
                   set_insert((x,y),result_map)
                 else
                   set_insert((x1,y1),result_map))
               m

  %%Was an axiom in Maps.sw:
  theorem update is
    fa(m,x,y,z) apply (update m x y) z =
                    (if z = x then Some y else apply m z)

  %%Copied from Maps.sw:
  theorem update_of_update_both is [a,b]
    fa(m: Map(a,b), keyone : a, keytwo : a, val1: b, val2 : b)
      update (update m keyone val1) keytwo val2 = (if keyone = keytwo then (update m keytwo val2) else (update (update m keytwo val2) keyone val1))

  % Remove the binding for key (if any).
  op [a,b] remove (m:Map(a,b)) (x:a) : Map(a,b) = 
    if (apply m x = None) then
      m  % No binding, so do nothing (could drop this case, but it may be faster to keep it)
    else
      set_fold empty_map
               (fn (result_map,(x1,y1)) ->
                  if x1 = x then
                    result_map % This is the pair to be removed.  Skip it.
                  else
                    set_insert((x1,y1),result_map)) % Copy everything else.
               m

  op [a,b] singletonMap (x:a) (y:b) : Map(a,b) = (update (empty_map) x y)

  op [a,b] domain (m : Map(a,b)) : Set a =
    set_fold empty_set 
             (fn (dom,(x1,y1))-> set_insert(x1, dom))
             m

  op [a,b] range (m:Map(a,b)) : Set b =
    set_fold empty_set
             (fn (range,(x1,x2))-> set_insert(x2, range))
             m

  % TODO: This doesn't seem well-formed (see the restrictions on
  % set_fold).  In particular, in what order should the elements of
  % the domain list appear?
  op [a,b] domainToList(m: Map(a,b)): List a =
    set_fold [] 
             (fn (dom, (x1,x2))-> x1 :: dom)
             m

  % TODO: This doesn't seem well-formed (see the restrictions on
  % set_fold).  In particular, in what order should the elements of
  % the range list appear?
  op [a,b] rangeToList (m: Map(a,b)): List b =
    set_fold []
             (fn (range, (x1,x2))-> x2 :: range)
             m

  op [a,b] size (m : Map(a,b)) : Nat = size (domain m)

  op [a,b] total? (s:Set a, m:Map(a,b)): Bool = (s subset domain m)

  op [a,b] TMApply(m:Map(a,b), x:a | x in? domain(m)): b =
    (case apply m x of
      | Some z -> z)
  op [a,b] TMApplyC(m:Map(a,b)) (x:a | x in? domain m): b = TMApply(m, x)

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn (m, x) -> update m x (f x)) s

  %% Added by Eric (just copied from Maps.sw):
  op [a,b,acc] foldable? (f : (a * b * acc -> acc)) : Bool =
    fa(key1:a, val1:b, key2:a, val2:b, accval:acc)
      ~(key1 = key2) =>   %% Excludes the case of the same key twice with different values (can't happen).
      f(key1,val1,f(key2,val2,accval)) = f(key2,val2,f(key1,val1,accval))

  op [Dom,Cod,a] foldi (f : (Dom * Cod * a -> a)) (acc:a) (m : Map (Dom,Cod)) : a =
    set_fold acc
             (fn (acc,(x,y)) -> f(x,y,acc))
             m 

  % Just copied from Maps.sw:
  op [a,b] Map_P (preda: a -> Bool, predb: b -> Bool) (m : Map(a,b)) : Bool =
    forall? (fn (key, val) -> preda key && predb val)
            m

  % Just copied from Maps.sw:
  op [a,b] forall? (p : a * b -> Bool) (m: Map (a,b)) : Bool =
    foldi (fn (key,val,acc) -> acc && p(key,val))
          true
          m

  op [a,b,c,d] isoMap: Bijection(a,c) -> Bijection(b,d) -> Bijection(Map(a, b), Map(c, d)) =
    fn iso_a -> fn iso_b -> foldi (fn (x, y, new_m) -> update new_m (iso_a x) (iso_b y)) empty_map

  % Just copied from Maps.sw:
  op [a,b] copyMap(m:Map(a,b)):Map(a,b) =
     set_fold (empty_map)
              (fn(newm:Map(a,b),x: {x:a | x in? (domain m)})-> update newm x (TMApply(m,x)))
              (domain m)

proof Isa Map__apply_Obligation_subtype
  oops
end-proof

proof Isa Map__map_apply_Obligation_subtype
  oops
end-proof

proof Isa Map__empty_map_Obligation_subtype
  apply(simp add: Map__no_duplicate_keys_p_def  Set__empty_set)
end-proof

proof Isa Map__update_Obligation_subtype
  oops
end-proof

proof Isa Map__update_Obligation_subtype0
  oops
end-proof

proof Isa Map__update_Obligation_subtype1
  oops
end-proof

proof Isa Map__update_Obligation_subtype2
  oops
end-proof

proof Isa Map__update
  sorry
end-proof

proof Isa Map__remove_Obligation_subtype
  oops
end-proof

proof Isa Map__remove_Obligation_subtype0
  oops
end-proof

proof Isa Map__domain_Obligation_subtype
  oops
end-proof

proof Isa Map__range_Obligation_subtype
  oops
end-proof

proof Isa Map__domainToList_Obligation_subtype
  oops
end-proof

proof Isa Map__rangeToList_Obligation_subtype
  oops
end-proof

proof Isa Map__mapFrom_Obligation_subtype
  oops
end-proof

proof Isa Map__mapUpdateSet_Obligation_subtype
  oops
end-proof

proof Isa Map__foldi_Obligation_subtype
  oops
end-proof

proof Isa isoMap_Obligation_subtype
  oops
end-proof

proof Isa Map__map_equality
  sorry
end-proof

proof Isa Map__copyMap_Obligation_subtype
  apply(rule Map__map_equality)
  apply(simp add: Map__TMApply_over_update Map__update)
end-proof

proof Isa Map__copyMap_Obligation_subtype
  oops
end-proof

proof Isa Map__not_in_p_when_apply_is_None
  sorry
end-proof

proof Isa Map__update_Obligation_subtype3
  sorry
end-proof

proof Isa Map__update_of_update_both
  sorry
end-proof

end-spec




%This was previously in the separate file MapsAsSetsRef.sw.
% the following morphism witnesses (once its proof obligations are
% discharged) that MapsAsSets is indeed a refinement of Maps

M = morphism Maps -> MapsAsSets {}    % {Map.map_apply +-> apply}

% proof obligations:
% the axioms characterizing the operations in Maps are satisfied
% by the definitions of those operations in MapsAsSets


proof Isa Map__total_p_def
  apply(auto simp add: Map__total_p_def Set__subset_def)
  apply(rule ext)
  apply(case_tac x, simp)
  apply(auto)
  apply(cut_tac Map__map_domain, auto)
  apply(cut_tac Map__map_domain, auto)
end-proof


proof Isa Map__empty_map
  sorry
end-proof

proof Isa Map__def_of_singletonMap
  sorry
end-proof

proof Isa Map__map_induction
  sorry
end-proof

proof Isa Map__map_domain
  sorry
end-proof

proof Isa Map__map_range
  sorry
end-proof

proof Isa Map__map_domainToList
  sorry
end-proof

proof Isa Map__map_rangeToList
  sorry
end-proof

proof Isa isoMap_def_Obligation_the
  sorry
end-proof

proof Isa isoMap_def
  sorry
end-proof

proof Isa Map__TMApply_def_Obligation_the
  sorry
end-proof

proof Isa Map__TMApply_def
  sorry
end-proof

proof Isa Map__map_apply_def
  sorry
end-proof

proof Isa Map__size_def
  sorry
end-proof

proof Isa Map__remove
  sorry
end-proof

%% may need to first fix set_fold:
proof Isa Map__map_foldi_empty
  apply(auto simp add: Map__foldi_def Map__empty_map_def)
  apply(rule Set__set_fold1)
  apply(auto simp add:  Map__foldable_p_def)
  apply(cut_tac c=accval and f = " (\<lambda>(acc0, x, y). f (x, y, acc0))" in Set__set_fold1)
  sorry
end-proof

proof Isa Map__map_foldi_update
  sorry
end-proof
