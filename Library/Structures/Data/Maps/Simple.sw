(* Polymorphic Maps
A stripped down version of Polymorphic.
*)

%% TODO Where do we give semantics to the operations in this file?


%% TODO Does this need to be a separate spec?  I guess it is refered to in a morphism in SimpleAsAList.
Map =
spec
  type Map (key,a)
endspec

Simple =
spec
  import Map

  op [key,a] emptyMap : Map (key,a)

  op [key,a] apply : Map(key,a) * key -> Option a
  op [key,a] eval  : Map(key,a) * key -> a

  op [key,a] update : Map (key,a) * key * a -> Map (key,a)
  op [a,key] remove : Map (key,a) * key -> Map (key,a)

  op [key,a] inDomain? : Map (key,a) * key -> Bool
  op [a,key] numItems : Map (key,a) -> Nat

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
  op filter  : [key,a] (a -> Bool) -> Map (key,a) -> Map (key,a)	  
  op filteri : [key,a] (key * a -> Bool) -> Map (key,a) -> Map (key,a)

  op mapPartial  : [key,a,b] (a -> Option b) -> Map (key,a) -> Map (key,b)
  op mapiPartial : [key,a,b] (key * a -> Option b) -> Map (key,a) -> Map (key,b)
  op compare : [a,key] (a * a -> Comparison)
       -> Map (key,a) -> Map (key,a) -> Comparison

  op submap? : [a,b] Map (a,b) * Map (a,b) -> Bool

  op allMap : [a,b] (a * b -> Bool) -> Map (a,b) -> Bool
  op existsMap : [a,b] (a * b -> Bool) -> Map (a,b) -> Bool

endspec
