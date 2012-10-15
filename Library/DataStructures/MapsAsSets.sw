% refinement of (finite) maps in terms of (finite) sets
Map qualifying
spec

  % we refine maps by means of sets: a map can be represented by a set of
  % pairs of type (a,b) such that no two pairs in the set have the same first
  % component but different second components (this is essentially the usual
  % set-theoretic definition)

  % clearly, there exist other ways to refine sets

  % first, we import sets

  import Sets

  % a map is a set of pairs (i.e., a binary relation) satisfying the
  % "functional requirement" (i.e., no element is mapped to different
  % elements)

  type Map(a,b) = {s : Set(a * b) |
                   fa(x,y1,y2) (x,y1) in? s & (x,y2) in? s => y1 = y2}

  % we (re-)define the operations on maps to operate on the
  % sets just defined and to be constructive

  % apply is defined by going through the set (by means of set_fold),
  % and looking for a pair whose first component is the given argument:
  % if one is found, the second component is returned (wrapped with
  % Some); if not, None is returned

  op [a,b] apply : Map(a,b) -> a -> Option b
  def apply m x = (set_fold None
                           (fn (result, (x1,y1)) ->
                               if x = x1 then Some y1 else result)
                           m)

  op [a,b] map_apply : Map(a,b) -> b -> a -> b
  def map_apply m b_default x = (set_fold b_default
                                   (fn (result, (x1,y1)) ->
                                      if x = x1 then y1 else result)
                                   m)

  % the empty map is represented by the empty set of pairs

  op [a,b] empty_map : Map(a,b)
  def empty_map = empty_set

  % there are two cases for updating a map: if a pair with the given
  % first component does not belong to the map, a suitable pair is inserted
  % into the set; otherwise, we go though the set (by means of set_fold)
  % reconstructing it the way it was, except for the pair with the given
  % first component

  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b)
  def update m x y = if apply m x = None
                     then set_insert((x,y),m)
                     else set_fold empty_map
                                   (fn (result_map,(x1,y1)) ->
                                       if x1 = x
                                       then set_insert((x,y),result_map)
                                       else set_insert((x1,y1),result_map))
                                   m

  % Remove the binding for key (if any).
  op [a,b] remove (m:Map(a,b)) (x:a) : Map(a,b) = 
    if apply m x = None then
      m  % No binding, so do nothing (could drop this case, but it may be faster to keep it)
    else set_fold empty_map
                  (fn (result_map,(x1,y1)) ->
                     if x1 = x
                     then result_map % This is the pair to be removed.  Skip it.
                     else set_insert((x1,y1),result_map)) % Copy everything else.
                  m

  op [a,b] singletonMap : a -> b -> Map(a,b)
  def [a,b] singletonMap x y = (update (empty_map) x y)

  op [a,b] domain: Map(a,b) -> Set a
  def [a,b] domain m = (set_fold empty_set 
                                (fn (dom:Set a,x:a*b)-> set_insert(x.1, dom))
                                m)
% TODO rename dom to ran here:
  def [a,b] range(m:Map(a,b)): (Set b) =
           set_fold empty_set 
                   (fn (dom:Set b,x:a*b)-> set_insert(x.2, dom))
                   m

  op [a,b] domainToList(m: Map(a,b)): List a =
    set_fold [] 
       (fn (dom:List a, x:a*b)-> x.1 :: dom)
       m

  op [a,b] rangeToList (m: Map(a,b)): List b =
    set_fold [] 
       (fn (ran:List b, x:a*b)-> x.2 :: ran)
       m

  op [a,b] size (m : Map(a,b)) : Nat = size (domain m)

 def [a,b] total? (s:Set(a), m:Map(a,b)):Boolean = (domain(m)=s)

  def [a,b] TMApply(m:Map(a,b),x:a | x in? domain(m)): b =
    (case apply m x of
      | Some z -> z)

%  op [a,b] mapFrom: Set a * (a -> b) ->  Map(a,b)
  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn  (m, x) -> update m x (f x)) s

  op [Dom,Cod,a] foldi (f : (Dom * Cod * a -> a)) (acc:a) (m : Map (Dom,Cod)) : a =
    set_fold acc
             (fn (acc,(x,y)) -> f(x,y,acc))
             m
    


end-spec

