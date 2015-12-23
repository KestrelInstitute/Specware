(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Naive Polymorphic Maps as Lists 

This is a hopelessly naive implementation of Maps as association Lists.
The eval is embarassing.
*)

spec 
  import /Library/PrettyPrinter/WadlerLindig
  import ../Polymorphic
  import /Library/Legacy/Utilities/System

  type Map (key,a) = List (key * a)

  % op emptyMap : [key,a] Map (key,a)
  def emptyMap = Nil

  % The following function will disappear when the library is restructured
  % with separate directories for total and partial maps.

  % op evalPartial : [key,a] Map(key,a) -> key -> Option a
  def evalPartial map x = 
    case map of
        [] -> None
      | (y,val)::tl -> 
           if x = y then
             (Some val)
           else
             evalPartial tl x

  % op eval : [key,a] Map(key,a) -> key -> a
  def eval map x = 
    case map of
        [] -> fail "inside eval"   % shame shame
      | (y,val)::tl -> 
           if x = y then
             val
           else
             eval tl x

  % op update : [key,a] Map (key,a) -> key -> a -> Map (key,a)
  def update map x y =
    case map of
        [] -> [(x,y)]
      | (u,v)::tl ->
          if (x = u) then
            Cons ((x,y),tl)
          else
            Cons ((u,v), update tl x y)

  % op remove : [a,key] Map (key,a) -> key -> Map (key,a)
  def remove map x =
    case map of
        [] -> []
      | (u,v)::y ->
           if u = x then
             y
           else
             Cons((u,v),remove y x)

(*
The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.
*)
  % op image : [key,a] Map (key,a) -> Set a

  % op imageToList : [key,a] Map (key,a) -> List a
  % def imageToList map =
  %  foldMap (fn values -> fn _ -> fn value -> Cons (value, values))
  %          []
  %          map      

  % op mapToList : [key,a] Map (key,a) -> List (key * a)
  def mapToList l = l

  % op domain : [key,a] Map (key,a) -> Set key
  % op domainToList : [key,a] Map (key,a) -> List key

  % op inDomain? : [key,a] Map (key,a) -> key -> Bool
  % def inDomain? map key =
  %   case map of
  %       [] -> false
  %     | (x,y)::tl -> (x = key) or (inDomain? tl key)

  % op numItems : [a,key] Map (key,a) -> Nat
  % op mapi : [key,a,b] (key -> a -> b) -> Map (key,a) -> Map (key,b)
(*
List the key/range pairs in order of appearance.
*)
  % op mapMap : [key,a,b] (a -> b) -> Map (key,a) -> Map (key,b)
  def mapMap f map =
    case map of
      | [] -> []
      | (x,y)::tl -> Cons ((x,f y), (mapMap f tl))

  % op foldMap : [Dom,Cod,a] (a -> Dom -> Cod -> a) -> a -> Map (Dom,Cod) -> a
  def foldMap f z map =
    case map of
      | [] -> z
      | (x,y)::tl -> foldMap f (f z x y) tl


  % op foldriDouble : [key1,key2,a,b] (key1 -> key2 -> a -> b -> b)
  %      -> b -> Map (key1, Map (key2, a)) -> b

  % TODO: make compose partial?
  % op compose : [dom,med,rng] Map (dom,med) -> Map (med,rng) -> Map (dom,rng)
  def compose m1 m2 = 
    foldMap (fn new_map -> fn dom -> fn med -> 
	     let cod = eval m2 med in % evalPartial ??
	     update new_map dom cod)
            emptyMap
            m1

  % op unionWith : [key,a] (a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map (key,a)
  % op unionWithi : [key,a] (key -> a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map (key,a)
  % op intersectWith : [key,a] (a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map(key,a)
  % op intersectWithi : [key,a] (key -> a -> a -> a)
  %      -> Map (key,a) -> Map (key,a) -> Map (key,a)
  % op filter  : [key,a] (a -> Bool) -> Map (key,a) -> Map (key,a)	  
  % op filteri : [key,a] (key -> a -> Bool) -> Map (key,a) -> Map (key,a)

  % op mapPartial : [key,a,b] (a -> Option b) -> Map (key,a) -> Map (key,b)
  def mapPartial f m = 
    let
      def g m key item = 
        case f item of
          | None -> m
          | (Some revised_item) -> update m key revised_item
    in
      foldMap g emptyMap m

  % op compare  : [a,key] (a * a -> Comparison) -> Map (key,a) -> Map (key,a) -> Comparison
  % op fromSet  : [a,b] Set  (a * b) -> Map (a, b)
  % op fromList : [a,b] List (a * b) -> Map (a, b)
  % op subset?  : [a,b] Map (a,b)           -> Map (a,b) -> Bool
  % op all      : [a,b] (a -> b -> Bool) -> Map (a,b) -> Bool
  % op exists   : [a,b] (a -> b -> Bool) -> Map (a,b) -> Bool
endspec
