% refinement of (finite) bags in terms of (finite) lists

BagsAsMaps =
BagsAsMaps qualifying
spec
 import Maps
  % we refine bags by means of maps: a bag can be represented by
  % a map from elements to their occurrence count in the bag

  type Bag a = Map(a, Nat)

  op bagin? infixl 100 : [a] a * Bag a -> Boolean
  def bagin?(x,b) =
    case apply b x of
      | Some y -> y > 0
      | None   -> false

  op occs : [a] a * Bag a -> Nat
  def occs(x,b) =
    case apply b x of
      | Some y -> y
      | None   -> 0

  op [a] subbag (b1:Bag a, b2: Bag a) infixl 200 : Boolean =
    %% size b1 <= size b2 &&   % seems wrong (map b1 may have many keys bound to 0 and still represent a subbag of b2)
    foldi (fn (x,y,r) -> r && y <= occs(x, b2)) true b1
  
  op empty_bag : [a] Bag a
  def empty_bag = empty_map

  op bag_insert : [a] a * Bag a -> Bag a
  def bag_insert(x, b) = update b x (occs(x, b) + 1)

  %op bag_union infixl 300 : [a] Bag a * Bag a -> Bag a
  op [a] \/ infixl 24 : Bag a * Bag a -> Bag a
  def \/(b1, b2) =
     foldi (fn (x,y,b) -> update b x (occs(x, b2) + y)) b1 b1

  % finally, bag_fold amounts to list_fold on a representing list

  op bag_fold : [a,b] b ->
                        {f : b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)} ->
                        Bag a ->
                        b
%   def bag_fold c f b = choose[Bag] (fn l -> list_fold c f l) b
  def bag_fold c f b =
    %% Could be more efficient
    foldi (fn (x,y,r) -> foldl (fn (r, z) -> f(r, z)) r (repeat x y)) c b

  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (\/) bs

  op bag_delete : [a] a * Bag a -> Bag a
  def bag_delete(x, b) =
    let old_n = occs(x, b) in
    if old_n = 0 then b
    else if old_n = 1 then remove b x
    else update b x (old_n - 1)

  op [a] -- infixl 25 : Bag a * Bag a -> Bag a
%%  op [a] bag_difference: Bag a * Bag a -> Bag a
  def --(b1, b2) =
    foldi (fn (x,y,b) -> let n2 = occs(x, b2) in
           if n2 >= y then remove b x
           else update b x (y - n2))
      b1 b1

  op [a] bag_filter (f: a -> Boolean) (b: Bag a): Bag a =
    foldi (fn (x,y,b) -> if f x then b else remove b x) b b

  op [a,b] bag_map (f: a -> b) (bg: Bag a): Bag b =
    foldi (fn (x,y,b) -> update b (f x) y) empty_map bg

  op [a] bag_size(b: Bag a): Nat =
    foldi (fn (x,y,sum) -> sum + y) 0 b


   %% Changed to match the change in Bags.sw. -Eric
   op [a] nt_subbag(As:Bag a, Bs:Bag a):Boolean =
     if As = empty_bag
       then Bs = empty_bag  %empty?(As)
       else As subbag Bs

% TODO don't copy this all over:
  op natMinus(m:Nat,n:Nat):Nat =
     if n<m
     then m - n
     else 0


end-spec


M = morphism Bags -> BagsAsMaps {Bag._ +-> BagsAsMaps._% ,
                                 % \/  +-> bag_union,
                                 % --  +-> bag_difference
                                 }
