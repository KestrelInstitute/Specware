(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MapsAsSTHTables =
MapsAsSTHTables qualifying
spec
  import Sets

  type Map(a, b)

  op MapSTHashtable.STH_apply : [key,a] Map(key,a) * key -> Option a
  op MapSTHashtable.STH_empty_map : [key,a] Map (key,a)
  op MapSTHashtable.STH_update : [key,a] Map (key,a) * key * a -> Map (key,a)
  op MapSTHashtable.STH_remove    : [a,key] Map (key,a) * key     -> Map (key,a)
  op MapSTHashtable.STH_domainToList : [key,a] Map (key,a) -> List key
  op MapSTHashtable.STH_imageToList : [key,a] Map (key,a) -> List a
  op MapSTHashtable.STH_eval  : [key,a] Map(key,a) * key -> a
  op MapSTHashtable.STH_foldi : [Dom,Cod,a] (Dom * Cod * a -> a) * a * Map (Dom,Cod) -> a
  op MapSTHashtable.STH_size : [key,a] Map(key,a) -> Nat

  %% Added by Eric (just copied from Maps.sw):
  op [a,b,acc] foldable? (f : (a * b * acc -> acc)) : Bool =
    fa(key1:a, val1:b, key2:a, val2:b, accval:acc)
      ~(key1 = key2) =>   %% Excludes the case of the same key twice with different values (can't happen).
      f(key1,val1,f(key2,val2,accval)) = f(key2,val2,f(key1,val1,accval))


  % This was added by Jim to the version of this file in the CRASH
  % library.  I am copying it here as well. -Eric, 11/15/12
  axiom sth_update is [key,a]
    fa(m:Map(key,a),x:key,y:a,z:key)
      STH_apply (STH_update (m, x, y), z) =
      (if z = x then Some y else STH_apply (m, z))

  op [a,b] apply : Map(a,b) -> a -> Option b =
    fn x -> fn y -> MapSTHashtable.STH_apply(x,y)
  op [a,b] empty_map :  Map(a,b) = MapSTHashtable.STH_empty_map
  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b) =
    fn m -> fn x -> fn y -> MapSTHashtable.STH_update(m,x,y)
  op remove : [a,b] Map (a,b) -> a -> Map (a,b) =
    fn m -> fn x -> MapSTHashtable.STH_remove(m, x)
  op [a,b] singletonMap : a -> b -> Map(a,b) =
    fn x -> fn y -> MapSTHashtable.STH_update(MapSTHashtable.STH_empty_map,x,y)
  %% Inefficient but best we can do with abstract sets
  op [a,b] domain(m: Map(a,b)): Set a =
    foldi (fn (x,y,r) -> set_insert_new(x,r)) empty_set m

  op [a,b] range (m: Map(a,b)): Set b =
    foldi (fn (x,y,r) -> set_insert(y,r)) empty_set m
  op [a,b] domainToList(m: Map(a,b)): List a = STH_domainToList m
  op [a,b] rangeToList (m: Map(a,b)): List b = STH_imageToList m
  op [a,b] total? (s: Set(a), m: Map(a,b)):Bool =
    set_fold true (fn (val,x) -> val && some?(MapSTHashtable.STH_apply(m,x))) s
  op [a,b] TMApply(m:Map(a,b),x:a | x in? domain(m)): b = MapSTHashtable.STH_eval(m,x)
  op [a,b] TMApplyC(m:Map(a,b)) (x:a | x in? domain m): b = TMApply(m, x)

   op foldi : [Dom,Cod,a] ((Dom * Cod * a -> a) | foldable?) -> a -> Map (Dom,Cod) -> a =
     fn f -> fn e -> fn m -> MapSTHashtable.STH_foldi(f,e,m)

  % Just copied from Maps.sw:
  op [a,b] forall? (p : a * b -> Bool) (m: Map (a,b)) : Bool =
    foldi (fn (key,val,acc) -> acc && p(key,val))
          true
          m

  op [a,b,c,d] isoMap: Bijection(a,c) -> Bijection(b,d) -> Bijection(Map(a, b), Map(c, d)) =
    fn iso_a -> fn iso_b -> foldi (fn (x, y, new_m) -> update new_m (iso_a x) (iso_b y)) empty_map

% how to handle apply outside the domain in MapSTHashtable?
  op [a,b] map_apply (m: Map(a,b))(null_elt:b)(x: a): b = MapSTHashtable.STH_eval(m,x)

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s
  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn  (m, x) -> update m x (f x)) s
  op [a,b] size(m: Map(a,b)): Nat = MapSTHashtable.STH_size m


  %% Just copied from Maps.sw:
  op [a,b] Map_P (preda: a -> Bool, predb: b -> Bool) (m : Map(a,b)) : Bool =
    forall? (fn (key, val) -> preda key && predb val)
            m

  %% Just copied from Maps.sw:
  op [a,b] copyMap(m:Map(a,b)):Map(a,b) =
     set_fold (empty_map)
              (fn(newm:Map(a,b),x: {x:a | x in? (domain m)})-> update newm x (TMApply(m,x)))
              (domain m)

proof Isa MapsAsSTHTables__domain_Obligation_subtype
  sorry
end-proof

%% TODO This is unprovable (think about the use of set_insert_new above).
proof Isa MapsAsSTHTables__domain_Obligation_subtype0
  sorry
end-proof

proof Isa MapsAsSTHTables__total_p_Obligation_subtype
  sorry
end-proof

proof Isa isoMap_Obligation_subtype
  sorry
end-proof

proof Isa isoMap_Obligation_subtype0
  sorry
end-proof

proof Isa MapsAsSTHTables__mapFrom_Obligation_subtype
  sorry
end-proof

proof Isa MapsAsSTHTables__mapUpdateSet_Obligation_subtype
  sorry
end-proof

proof Isa MapsAsSTHTables__range_Obligation_subtype
  sorry
end-proof

proof Isa MapsAsSTHTables__Map_P_Obligation_subtype
  apply(auto simp add: MapsAsSTHTables__foldable_p_def)
end-proof

%% translated from the proof in Maps.sw:
proof Isa MapsAsSTHTables__forall_p_Obligation_subtype
  apply(auto simp add: MapsAsSTHTables__foldable_p_def)
end-proof


proof Isa MapsAsSTHTables__copyMap_Obligation_subtype
  oops
end-proof

proof Isa MapsAsSTHTables__copyMap_Obligation_subtype0
  apply(auto simp add: Set__Set_P_def Set__forall_p_in_self)
end-proof


end-spec


M = morphism Maps -> MapsAsSTHTables {}

proof Isa Map__map_equality
  sorry
end-proof

proof Isa Map__empty_map
  sorry
end-proof

proof Isa Map__update
  sorry
end-proof

proof Isa Map__singletonMap_def
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

proof Isa Map__total_p_def
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

proof Isa Map__map_foldi_empty
  sorry
end-proof

proof Isa Map__map_foldi_update
  sorry
end-proof

