(* Polymorphic Maps
A stripped down version of Polymorphic.
*)

Map =
spec
  type Map (key,a)
endspec

Simple =
spec
  import Map

  op emptyMap : [key,a] Map (key,a)

  op apply : [key,a] Map(key,a) * key -> Option a
  op eval  : [key,a] Map(key,a) * key -> a

  op update : [key,a] Map (key,a) * key * a -> Map (key,a)
  op remove : [a,key] Map (key,a) * key -> Map (key,a)

  op inDomain? : [key,a] Map (key,a) * key -> Boolean
  op numItems : [a,key] Map (key,a) -> Nat

(* The functions that follow come in two varieties. All take functions
that operate on elements in the tree. For those with an `i' suffix, the
function is applied to both the key and the value. For those without
the `i' suffux, the supplied function is applied to only the values.

The next pair map a supplied function across the entries in the map.
*)
  op mapi : [key,a,b] (key * a -> b) -> Map (key,a) -> Map (key,b)
  op map  : [key,a,b] (a -> b) -> Map (key,a) -> Map (key,b)

(* Only useful with side-effects. *)
  op app   : [key,a] (a -> ()) -> Map (key,a) -> ()
  op appi  : [key,a] (key * a -> ()) -> Map (key,a) -> ()

  op foldi : [Dom,Cod,a] (Dom * Cod * a -> a) -> a -> Map (Dom,Cod) -> a


(* The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.
*)
  op imageToList : [key,a] Map (key,a) -> List a

(* List the key/range pairs in order of appearance. *)
  op mapToList : [key,a] Map (key,a) -> List (key * a)
  op domainToList : [key,a] Map (key,a) -> List key
  op unionWith : [key,a] (a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
  op unionWithi : [key,a] (key * a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
  op intersectWith : [key,a] (a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map(key,a)
  op intersectWithi : [key,a] (key * a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
  op filter  : [key,a] (a -> Boolean) -> Map (key,a) -> Map (key,a)	  
  op filteri : [key,a] (key * a -> Boolean) -> Map (key,a) -> Map (key,a)

  op mapPartial  : [key,a,b] (a -> Option b) -> Map (key,a) -> Map (key,b)
  op mapiPartial : [key,a,b] (key * a -> Option b) -> Map (key,a) -> Map (key,b)
  op compare : [a,key] (a * a -> Comparison)
       -> Map (key,a) -> Map (key,a) -> Comparison

  op submap? : [a,b] Map (a,b) * Map (a,b) -> Boolean

  op allMap : [a,b] (a * b -> Boolean) -> Map (a,b) -> Boolean
  op existsMap : [a,b] (a * b -> Boolean) -> Map (a,b) -> Boolean
endspec
