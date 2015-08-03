(* Maps as functions to option types, in the same manner as
/Library/General/Map, except that here we use "IMap" (for "Isabelle map") in
place of "Map" so that it is compatible with /Library/DataStructures/Maps.sw. *)

IMap qualifying spec
import ISet

type IMap(a,b) = a -> Option b

op [a,b] domain (m:IMap(a,b)) : ISet a = fn x:a -> m x ~= None

op [a,b] empty : IMap (a,b) = fn x -> None

op [a,b] update (m: IMap(a,b)) (x:a) (y:b) : IMap(a,b) =
  fn z:a -> if z = x then Some y else m z

(* True iff map1 has at least all the bindings of map2 *)
op [a,b] submap? (map1: IMap (a,b), map2: IMap (a,b)) : Bool =
  fa (x) x memb? (domain map1) => map1 x = map2 x


op [a,b] fromAssocList
   (alist: List (a * b) | let (xs,_) = unzip alist in noRepetitions? xs)
   : IMap (a, b) =
  let (xs,ys) = unzip alist in
  fn x:a -> if x in? xs then Some (ys @ (positionOf(xs,x))) else None


proof Isa Thy_Morphism Map
  type IMap.IMap     -> map
  IMap.domain        -> dom
  IMap.empty         -> empty
end-proof

end-spec
