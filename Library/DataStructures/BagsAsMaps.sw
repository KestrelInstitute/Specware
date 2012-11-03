% refinement of (finite) bags in terms of (finite) maps: A bag can be
% represented by a map from elements to their occurrence count in the
% bag.  I guess this representation is not unique: An element not
% present in the bag could either be paired with a count of 0 in the
% map, or have no pair in the map at all.

BagsAsMaps =
BagsAsMaps qualifying
spec
  import Maps

  type Bag a = Map(a, Nat)

  op [a] bagin? (x:a, b:Bag a) infixl 100 : Boolean =
    case apply b x of
      | Some y -> y > 0
      | None   -> false

  op [a] occs(x:a, b:Bag a) : Nat =
    case apply b x of
      | Some y -> y
      | None   -> 0

  op [a] subbag (b1:Bag a, b2: Bag a) infixl 200 : Boolean =
    %% size b1 <= size b2 &&   % seems wrong (map b1 may have many keys bound to 0 and still represent a subbag of b2)
    foldi (fn (x,y,r) -> r && y <= occs(x, b2)) true b1
  
  op [a] empty_bag : Bag a = empty_map

  op [a] bag_insert(x:a, b:Bag a) : Bag a = update b x (occs(x, b) + 1)

  %op bag_union infixl 300 : [a] Bag a * Bag a -> Bag a
  %% TTODO seems wrong: What about elements in b2 but not in b1?
  op [a] \/ (b1:Bag a, b2:Bag a) infixl 24 : Bag a =
    foldi (fn (x,y,b) -> update b x (occs(x, b2) + y)) b1 b1

  % finally, bag_fold amounts to list_fold on a representing list

%   def bag_fold c f b = choose[Bag] (fn l -> list_fold c f l) b
  op [a,b] bag_fold (c:b)
                    (f : b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y))
                    (bag : Bag a) : b =
    %% Could be more efficient
    foldi (fn (x,y,r) -> foldl (fn (r, z) -> f(r, z)) %TODO just say f here?
                               r 
                               (repeat x y)) 
          c 
          bag

  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (\/) bs

  % delete one occurrence of x from b
  op [a] bag_delete(x:a, b:Bag a) : Bag a =
    let old_n = occs(x, b) in
    if old_n = 0 then b
    else if old_n = 1 then remove b x
    else update b x (old_n - 1)

%%  op [a] bag_difference: Bag a * Bag a -> Bag a
  op [a] -- (b1: Bag a, b2: Bag a) infixl 25 : Bag a =
    foldi (fn (x,y,b) ->
            let n2 = occs(x, b2) in
            if n2 >= y then
              remove b x
            else
              update b x (y - n2))
          b1  %or could start out with an empty accumulator?
          b1

  %or could start out with an empty accumulator?
  op [a] bag_filter (f: a -> Boolean) (b: Bag a): Bag a =
    foldi (fn (x,y,b) -> if f x then b else remove b x) b b

  %TTODO what if two of the keys in bg map to the same value under f?
  op [a,b] bag_map (f: a -> b) (bg: Bag a) : Bag b =
    foldi (fn (x,y,b) -> update b (f x) y) empty_map bg

  op [a] bag_size (b: Bag a) : Nat =
    foldi (fn (x,y,sum) -> sum + y) 0 b

   %% Changed to match the change in Bags.sw. -Eric
   op [a] nt_subbag(As:Bag a, Bs:Bag a):Boolean =
     if As = empty_bag
       then Bs = empty_bag  %empty?(As)
       else As subbag Bs

% TODO Perhaps this should be in a library (currently, it is in several places).
  op natMinus (m:Nat, n:Nat) : Nat =
    if n<m
    then m - n
    else 0

end-spec


M = morphism Bags -> BagsAsMaps {Bag._ +-> BagsAsMaps._% ,
                                 % \/  +-> bag_union,
                                 % --  +-> bag_difference
                                 }
