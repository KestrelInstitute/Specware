(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% TODO Does the code for the MapVec functions come from:
% Specware/Library/Structures/Data/Maps/Handwritten/Lisp/MapAsVector.lisp?
% TODO compare to /Library/Structures/Data/Maps/MapVec.sw

%TODO Does this only work for maps where the domain is Nat?

MapsAsVectors =
MapsAsVectors qualifying
spec
  import Sets
  import /Library/Structures/Data/Maps/MapVec

  %% This was added by Jim to the version of this file in the CRASH
  %% library.  I am copying it here as well. -Eric, 11/15/12

  %% this is used by Setf machinery to identify accessor/setter pairs,
  %% facilitating rewrites such as:
  %%   setf (lhs, V_update (lhs, indices, value))
  %%    =>
  %%   V_update (lhs, indices, value)
  axiom v_update is [key,a]
    fa(m:Map(key,a),x:key,y:a,z:key)
      V_apply (V_update (m, x, y), z) =
      (if z = x then Some y else V_apply (m, z))

  op [a,b] apply : Map(a,b) -> a -> Option b =
    fn x -> fn y -> MapVec.V_apply(x,y)

  op [a,b] empty_map : Map(a,b) = MapVec.V_empty_map

  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b) =
    fn m -> fn x -> fn y -> MapVec.V_update(m,x,y)

  %% this is used by Setf machinery to identify accessor/setter pairs,
  %% facilitating rewrites such as:
  %%   setf (lhs, update lhs indices value)
  %%    =>
  %%   update lhs indices value
  % axiom update is [key,a]
  %   fa (m:Map(key,a), x:key, y:a, z:key)
  %     V_eval (update m x y, z) =
  %     (if z = x then y else V_eval (m, z))

  op [a,b] singletonMap : a -> b -> Map(a,b) =
    fn x -> fn y -> MapVec.V_update(MapVec.V_empty_map,x,y)

  %% Inefficient but best we can do with abstract sets
  op [a,b] domain(m: Map(a,b)): Set a =
    V_foldi (fn (x,_,s) -> set_insert_new(x,s), empty_set, m)

  op [a,b] range (m: Map(a,b)): Set b =
    foldl (fn (s,x) -> set_insert(x,s)) empty_set (MapVec.V_imageToList m)  % was rangeToList

  op [a,b] domainToList(m: Map(a,b)): List a = V_domainToList m

  op [a,b] rangeToList (m: Map(a,b)): List b = V_imageToList m

  op [a,b] total? (s: Set(a), m: Map(a,b)):Bool =
    set_fold true (fn (val,x) -> val && some?(MapVec.V_apply(m,x))) s

  op [a,b] TMApply(m:Map(a,b),x:a | x in? domain(m)): b = MapVec.V_eval(m,x)
  op [a,b] TMApplyC(m:Map(a,b)) (x:a | x in? domain m): b = TMApply(m, x)

  op [a,b] map_apply (m: Map(a,b))(null_elt:b)(x: a): b = MapVec.V_map_eval(m,x,null_elt)

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn  (m, x) -> update m x (f x)) s

  %% Just copied from Maps.sw
  op [a,b] copyMap(m:Map(a,b)):Map(a,b) =
     set_fold (empty_map)
              (fn(newm:Map(a,b),x: {x:a | x in? (domain m)})-> update newm x (TMApply(m,x)))
              (domain m)

  %% Added by Eric:
  op remove : [a,b] Map (a,b) -> a -> Map (a,b) = fn x -> fn y -> MapVec.V_remove(x,y)

  %% Added by Eric (just copied from Maps.sw):
  op [a,b,acc] foldable? (f : (a * b * acc -> acc)) : Bool =
    fa(key1:a, val1:b, key2:a, val2:b, accval:acc)
      ~(key1 = key2) =>   %% Excludes the case of the same key twice with different values (can't happen).
      f(key1,val1,f(key2,val2,accval)) = f(key2,val2,f(key1,val1,accval))

  %% Added by Eric:
  op foldi : [Dom,Cod,a] ((Dom * Cod * a -> a) | foldable?) -> a -> Map (Dom,Cod) -> a =
    fn f -> fn acc -> fn map -> MapVec.V_foldi(f,acc,map)

  % Just copied from Maps.sw:
  op [a,b] forall? (p : a * b -> Bool) (m: Map (a,b)) : Bool =
    foldi (fn (key,val,acc) -> acc && p(key,val))
          true
          m

  %% Just copied from Maps.sw:
  op [a,b] Map_P (preda: a -> Bool, predb: b -> Bool) (m : Map(a,b)) : Bool =
    forall? (fn (key, val) -> preda key && predb val)
            m

  op [a,b,c,d] isoMap: Bijection(a,c) -> Bijection(b,d) -> Bijection(Map(a, b), Map(c, d)) =
    fn iso_a -> fn iso_b -> foldi (fn (x, y, new_m) -> update new_m (iso_a x) (iso_b y)) empty_map

  %% Added by Eric:
  op [a,b] size: Map(a,b) -> Nat = fn m -> size (domain m)

proof Isa domain_Obligation_subtype
  sorry
end-proof
 
proof Isa total_p_Obligation_subtype
  sorry
end-proof
 
proof Isa mapFrom_Obligation_subtype
  sorry
end-proof
 
proof Isa mapUpdateSet_Obligation_subtype
  sorry
end-proof
 
proof Isa isoMap_Obligation_subtype
  sorry
end-proof

proof Isa isoMap_Obligation_subtype0
  sorry
end-proof

proof Isa MapsAsVectors__Map_P_Obligation_subtype
  apply(auto simp add: MapsAsVectors__foldable_p_def)
end-proof

%% translated from the proof in Maps.sw:
proof Isa MapsAsVectors__forall_p_Obligation_subtype
  apply(auto simp add: MapsAsVectors__foldable_p_def)
end-proof

proof Isa MapsAsVectors__copyMap_Obligation_subtype
  oops
end-proof

proof Isa MapsAsVectors__copyMap_Obligation_subtype0
  oops
end-proof

end-spec



M = morphism Maps -> MapsAsVectors {}

proof Isa map_equality
  sorry
end-proof
 
proof Isa empty_map
  sorry
end-proof
 
proof Isa update
  sorry
end-proof
 
proof Isa Map__singletonMap_def
  apply(simp add: MapsAsVectors__singletonMap_def MapsAsVectors__update_def MapsAsVectors__empty_map_def)
end-proof
 
proof Isa map_induction
  sorry
end-proof
 
proof Isa map_domain
  sorry
end-proof
 
proof Isa map_range
  sorry
end-proof
 
proof Isa map_domainToList
  sorry
end-proof
 
proof Isa map_rangeToList
  sorry
end-proof
 
proof Isa isoMap_def_Obligation_the
  sorry
end-proof

proof Isa isoMap_def
  sorry
end-proof

proof Isa TMApply_def_Obligation_the
  sorry
end-proof
 
proof Isa TMApply_def
  sorry
end-proof
 
proof Isa total_p_def
  sorry
end-proof
 
proof Isa map_apply_def
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

proof Isa Map__Map_P_def
  apply(auto simp add: MapsAsVectors__Map_P_def)
end-proof
