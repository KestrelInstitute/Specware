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

   op foldi : [Dom,Cod,a] (Dom * Cod * a -> a) -> a -> Map (Dom,Cod) -> a =
     fn f -> fn e -> fn m -> MapSTHashtable.STH_foldi(f,e,m)

% how to handle apply outside the domain in MapSTHashtable?
  op [a,b] map_apply (m: Map(a,b))(null_elt:b)(x: a): b = MapSTHashtable.STH_eval(m,x)

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s
  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn  (m, x) -> update m x (f x)) s
  op [a,b] size(m: Map(a,b)): Nat = MapSTHashtable.STH_size m


%% TODO This is unprovable (think about the use of set_insert_new above).
proof Isa MapsAsSTHTables__domain_Obligation_subtype
  sorry
end-proof

proof Isa MapsAsSTHTables__total_p_Obligation_subtype
  sorry
end-proof

proof Isa MapsAsSTHTables__mapFrom_Obligation_subtype
  sorry
end-proof

proof Isa MapsAsSTHTables__mapUpdateSet_Obligation_subtype
  sorry
end-proof
    
end-spec


M = morphism Maps -> MapsAsSTHTables {}
