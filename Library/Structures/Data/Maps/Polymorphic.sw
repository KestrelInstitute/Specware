(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Polymorphic Maps}
This to be deprecated in favour of Maps/Polymorphic/Finite.sw %TODO That file doesn't exist?

A rather inflated signature for maps. These are maps that are polymorphic
in both their domain and codomain.

This was distilled from the
signature for splay maps. Some thought should go into pruning this
down.

The operator eval should return Option a (rather tha a). But this
makes the spec implementing category theory very ugly. On the other hand,
the version below does not agree with the various implementations of Maps

To avoid a name clash with the operators in Sets, we use emptyMap,
foldMap and mapMap. The latter is a lousy name. The whole policy needs
thought.

\begin{spec}
spec {
  % import /Library/Structures/Data/Sets/Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  type Map (key,a)

  op emptyMap : fa(key,a) Map (key,a)

  % The following function will disappear when the library is refactored.
  op evalPartial : fa(key,a) Map(key,a) -> key -> Option a
  op eval : fa(key,a) Map(key,a) -> key -> a

  op update : fa (key,a) Map (key,a) -> key -> a -> Map (key,a)
  op remove : fa (a,key) Map (key,a) -> key -> Map (key,a)
\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

begin{spec}
  op image : fa (key,a) Map (key,a) -> Set a
  op imageToList : fa(key,a) Map (key,a) -> List a
end{spec}

List the key/range pairs in order of appearance.

\begin{spec}
  op mapToList : fa(key,a) Map (key,a) -> List (key * a)
\end{spec}

begin{spec}
  op domain : fa(key,a) Map (key,a) -> Set key
  op domainToList : fa(key,a) Map (key,a) -> List key
end{spec}

begin{spec}
  op inDomain? : fa(key,a) Map (key,a) -> key -> Bool
  op numItems : fa(a,key) Map (key,a) -> Nat
end{spec}

The functions that follow come in two varieties. All take functions
that operate on elements in the tree. For those with an `i' suffix, the
function is applied to both the key and the value. For those without
the `i' suffux, the supplied function is applied to only the values.

The next maps a supplied function across the entries in the map.
begin{spec}
  op mapi : fa(key,a,b) (key -> a -> b) -> Map (key,a) -> Map (key,b)
end{spec}

\begin{spec}
  op foldMap : fa(Dom,Cod,a) (a -> Dom -> Cod -> a) -> a -> Map (Dom,Cod) -> a
  op mapMap : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
  % op foldri : fa(key,a,b)  (key -> a -> b -> b) -> b -> Map (key,a) -> b
  % op foldr : fa(key,a,b) (a -> b -> b) -> b -> Map (key,a) -> b
  % op foldli : fa(key,a,b) (key -> a -> b -> b) -> b -> Map (key,a) -> b
  % op foldl : fa(key,a,b) (a -> b -> b) -> b -> Map (key,a) -> b
\end{spec}

Don't understand the next one.

begin{spec}
  op foldriDouble : fa(key1,key2,a,b) (key1 -> key2 -> a -> b -> b)
       -> b -> Map (key1, Map (key2, a)) -> b
end{spec}

Compose two maps. (compose f g = f;g). Perhaps it should be the other
way around.

\begin{spec}
  op compose : fa(dom,med,rng) Map (dom,med) -> Map (med,rng) -> Map (dom,rng)
\end{spec}

begin{spec}
  op unionWith : fa(key,a) (a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
  op unionWithi : fa(key,a) (key -> a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
end{spec}

begin{spec}
  op intersectWith : fa(key,a) (a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map(key,a)
  op intersectWithi : fa(key,a) (key -> a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
end{spec}

begin{spec}
  op filter  : fa(key,a) (a -> Bool)        -> Map (key,a) -> Map (key,a)	  
  op filteri : fa(key,a) (key -> a -> Bool) -> Map (key,a) -> Map (key,a)
end{spec}

\begin{spec}
  op mapPartial : fa(key,a,b) (a -> Option b) -> Map (key,a) -> Map (key,b)
\end{spec}

Form a map from an association sets and lists. 

begin{spec}
  op compare : fa(a,key) (a * a -> Comparison)
       -> Map (key,a) -> Map (key,a) -> Comparison
  op fromSet : fa (a,b) Set (a * b) -> Map (a, b)
  op fromList : fa (a,b) List (a * b) -> Map (a, b)
end{spec}

begin{spec}
  op subset? : fa (a,b) Map (a,b) -> Map (a,b) -> Bool
end{spec}

begin{spec}
  op all    : fa (a,b) (a -> b -> Bool) -> Map (a,b) -> Bool
  op exists : fa (a,b) (a -> b -> Bool) -> Map (a,b) -> Bool
end{spec}

Pretty printing. As in sets, it is not clear that this belongs in this
spec or in specific refinements of it. Note that the map is printed
in the reverse order to the way it it traversed by foldMap.

\begin{spec}
  op ppMap : fa (a,b) (a -> WLPretty) -> (b -> WLPretty) -> Map (a,b) -> WLPretty
  def ppMap ppKey ppValue map =
     ppSep ppNewline (foldMap (fn l -> fn dom -> fn cod
               -> Cons (ppConcat [
                          ppKey dom,
                          ppString " +-> ",
                          ppValue cod], l)) [] map)
\end{spec}

\begin{spec}
}
\end{spec}
