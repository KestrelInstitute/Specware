% refinement of (finite) sets in terms of (finite) characteristic maps. In fact we maintain the invariant that
% the map is undefined where the element is not in the set. I.e. the set is the domain of the map.
SetsAsMaps =
SetsAsMap qualifying
spec

  import Maps

  type Set a = Map(a, Bool)

% This is imported via Set in Map theory
  op in? infixl 20 : [a] a * Set a -> Bool
  def in?(x,s) = apply s x = Some true

  % set containment just amounts to map containment, because there are no
  % repeated elements

  op subset infixl 20 : [a] Set a * Set a -> Bool
  def subset(s1,s2) =
    Map.size s1 <= Map.size s2
      && foldi (fn (x, _, val) -> val && x in? s2) true s1

  op empty_set : [a] Set a
  def empty_set = empty_map

  % to insert an element into a repetition-free map representing a set,
  % we have to first check whether the element occurs in the map: if yes,
  % the map is unchanged; if not, the element is inserted into the map

  op set_insert : [a] a * Set a -> Set a
  def set_insert(x,s) = update s x true

  %% Not useful for this representation
  op set_insert_new: [a] a * Set a -> Set a
  def set_insert_new(x,s) = update s x true

  % to take the union of two sets, again we need to ensure that the resulting
  % map is repetition-free; we use a map_fold, starting with the first map,
  % to go through the second map and insert its elements into the first if
  % they are not present in the first already (using set_insert just defined)

  op \/ infixl 300 : [a] Set a * Set a -> Set a
  def \/(s1,s2) = foldi (fn(x,_,result) -> set_insert(x,result))
                    s1  s2

  op /\ infixl 300 : [a] Set a * Set a -> Set a
  def /\(s1,s2) = foldi (fn(x,_,result) -> if x in? s1 
                                             then set_insert(x,result)
                                             else result)
                    empty_set s2

  % finally, set_fold amounts to map_fold on the representing map

  op set_fold : [a,b] b ->
                        {f : b * a -> b |
                         (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                         (fa(x,y)   f(f(x,y), y) = f(x,y))} ->
                        Set a ->
                        b
  def set_fold c f s = foldi (fn (x, _, result) -> f(result, x)) c s

  op [a] //\\ (ss:Set (Set a)) : Set a =
    set_fold empty_set (/\) ss

  op [a] \\// (ss:Set (Set a)) : Set a =
    set_fold empty_set (\/) ss

  op set_delete : [a] a * Set a -> Set a
  def set_delete(x,s) = remove s x

  op [a] -- infixl 25 : Set a * Set a -> Set a
  def --(s1,s2) = foldi (fn (x, _, result) -> remove result x)
                    s1 s2

  op [a] set_difference: Set a * Set a -> Set a
  def set_difference(s1,s2) = (s1 -- s2)  % map_difference(s1,s2)

  op [a] size(s: Set a): Nat = Map.size s

  op [a] filter(p: a -> Bool) (s: Set a): Set a =
     foldi (fn (x,_,result) -> if p x then set_insert(x, result) else result)
       empty_set s
  op [a,b] map(f: a -> b) (s: Set a): Set b =
    foldi (fn (x,_,result) -> set_insert(f x, result))
       empty_set s

  % Changed to match the change in Sets.sw -Eric
  op [a] nt_subset(As:Set a, Bs:Set a): Bool =
    if As = empty_set
       then Bs=empty_set  %empty?(As)
       else As subset Bs

end-spec

M = morphism Sets -> SetsAsMaps {Set._ +-> SetsAsMap._}
