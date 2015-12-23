(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
  import /Library/General/Sets
  op  uncurry : [a, b, c] (a -> b -> c) -> a * b -> c
  def uncurry f (x, y) = f x y

  type Seq a = List a

  op  nOcc : [a] Seq a -> a -> Nat
  def nOcc s x = length(filter(fn z -> z = x) s)

  op  members : [a] Seq a -> Set a
  def members s = posNat? o nOcc s

  (* This should be restricted to maps with unique keys: *)
  type Map(a, b) = List(a * b)

  op  dom : [a, b] Map(a, b) -> Set a
  def dom m x = exists((fn (k, _) -> k = x)) m

  op  mapWithKey : [a, b] Set(Map(a, b) * a)
  def mapWithKey = uncurry(dom)

  type MapWithKey(a, b) = (Map(a, b) * a | mapWithKey)

  op  @? infixl 30 : [a, b] Map(a, b) * a -> Option b
  def @? (map, key) =
    let def lookupkey m =
          (case m of
              | Nil -> None
              | Cons ((k, v), t) ->
                if k = key then Some v else lookupkey t)
    in
    lookupkey map

  op  @ infixl 30 : [a, b] MapWithKey(a, b) -> b
  def @ (map, key) =
    let def lookupkey m =
          (case m of
              | Cons((k, v), t) -> if k = key then v else lookupkey t)
    in
    lookupkey map

  op  mapUpdate : [a, b] Map(a, b) * a * b -> Map(a, b)
  def mapUpdate(map, key, assoc) = Cons((key, assoc), map)

  conjecture @?@@ is [a, b]
     fa(m : Map(a, b), x : a) dom m x => m @? x = Some(m @ x)

  op  keys : [a, b] Map(a, b) -> Seq a
  def keys = map (project 1)

  op  associates : [a, b] Map(a, b) -> Seq b
  def associates = map (project 2)

  op  mapMap : [a,b,a1,b1] (a->a1) * (b->b1) -> Map(a, b) -> Map(a1, b1)
  def mapMap(f,g) = map(fn(x, y) -> (f x, g y))

  op  without infixl 25 : [a] Seq a * Seq a -> Seq a
  def without(x, y) = filter((~) o members y) x

endspec
