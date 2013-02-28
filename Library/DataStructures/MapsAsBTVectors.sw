%% The code for this may be in:
%% Specware\Library\Structures\Data\Maps\Handwritten\Lisp\MapAsBTVector.lisp

MapsAsBTVectors =
MapsAsBTVectors qualifying
spec
  import Sets

  type Map(a,b)

  op MapBTV.BTV_apply : [key,a] Map(key,a) * key -> Option a
  op MapBTV.BTV_empty_map : [key,a] Map (key,a)
  op MapBTV.BTV_update :  [key,a] Map (key,a) * key * a -> Map (key,a)
  op MapBTV.BTV_domainToList : [key,a] Map (key,a) -> List key
  op MapBTV.BTV_imageToList : [key,a] Map (key,a) -> List a                   % was rangeToList
  op MapBTV.BTV_eval  : [key,a] Map(key,a) * key -> a
  op MapBTV.BTV_foldi : [key, a, b] (key * a * b -> b) * b * Map(key,a) -> b
  op MapBTV.BTV_remove      : fa (a,key) Map (key,a) * key -> Map (key,a)

  % This was added by Jim to the version of this file in the CRASH
  % library.  I am copying it here as well. -Eric, 11/15/12
  axiom btv_update is [key,a]
    fa(m:Map(key,a),x:key,y:a,z:key)
      BTV_apply (BTV_update (m, x, y), z) =
      (if z = x then Some y else BTV_apply (m, z))

  op [a,b] apply : Map(a,b) -> a -> Option b =
    fn x -> fn y -> MapBTV.BTV_apply(x,y)

  op [a,b] empty_map :  Map(a,b) = MapBTV.BTV_empty_map

  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b) =
    fn m -> fn x -> fn y -> MapBTV.BTV_update(m,x,y)

  op [a,b] singletonMap : a -> b -> Map(a,b) =
    fn x -> fn y -> MapBTV.BTV_update(MapBTV.BTV_empty_map,x,y)

  %% Inefficient but best we can do with abstract sets
  op [a,b] domain(m: Map(a,b)): Set a =
    BTV_foldi (fn (x,_,s) -> set_insert_new(x,s), empty_set, m)

  op [a,b] range (m: Map(a,b)): Set b =
    foldl (fn (s,x) -> set_insert(x,s)) empty_set (MapBTV.BTV_imageToList m)  % was rangeToList

  op [a,b] domainToList(m: Map(a,b)): List a = BTV_domainToList m

  op [a,b] rangeToList (m: Map(a,b)): List b = BTV_imageToList m

  op [a,b] total? (s: Set(a), m: Map(a,b)):Bool =
    set_fold true (fn (val,x) -> val && some?(MapBTV.BTV_apply(m,x))) s
  op [a,b] TMApply(m:Map(a,b),x:a | x in? domain(m)): b = MapBTV.BTV_eval(m,x)

% how to handle apply outside the domain in MapBTV?
  op [a,b] map_apply (m: Map(a,b))(null_elt:b)(x: a): b = MapBTV.BTV_eval(m,x)

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s
  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn  (m, x) -> update m x (f x)) s

 %Added by Eric:
  op remove : [a,b] Map (a,b) -> a -> Map (a,b) = fn x -> fn y -> MapBTV.BTV_remove(x,y)

 % Added by Eric:
  op foldi : [Dom,Cod,a] (Dom * Cod * a -> a) -> a -> Map (Dom,Cod) -> a =
    fn f -> fn acc -> fn map -> MapBTV.BTV_foldi(f,acc,map)

  %Added by Eric:
  op [a,b] size: Map(a,b) -> Nat = fn m -> size (domain m)

end-spec

% The same as MapsAsBTVectorsRef, which has been removed.
M = morphism Maps -> MapsAsBTVectors {}
