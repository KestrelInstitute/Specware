(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Monomorphic Maps}

A rather inflated signature for maps. This was distilled from the
signature for splay maps. Some thought should go into pruning this
down.

Like the polymorphic sets, there should be a function which yields the
domain and codomains of the map as sets. To do this propery requires
that we import two monomorphic copies of Sets.  Then this creates an
extra burden to rename things carefully when we import these maps. Also,
most of what appears in Sets is not needed. Needs thought.

We are likely to have sets in the same context as maps. For this reason
we use emptyMap and foldMap but would prefer to use empty and fold. Needs
thought.

\begin{spec}
spec {
  import /Library/PrettyPrinter/WadlerLindig
  import Cod 
  import Dom

  type Map

  op emptyMap : Map 
  op update : Map -> Dom -> Cod -> Map

  % op eval : Map -> Dom -> Option Cod
  op eval : Map -> Dom -> Cod
  op remove : Map -> Dom -> Map
\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

\begin{spec}
  op imageToList : Map -> List Cod
\end{spec}

List the key/range pairs in order of appearance.

\begin{spec}
  op mapToList : Map -> List (Dom * Cod)
  op domainToList : Map -> List Dom
\end{spec}

\begin{spec}
  op inDomain? : Map -> Dom -> Bool
  op numItems : Map -> Nat
\end{spec}

The functions that follow come in two varieties. All take functions
that operate on elements in the tree. For those with an `i' suffix, the
function is applied to both the key and the value. For those without
the `i' suffux, the supplied function is applied to only the values.

The next pair map a supplied function across the entries in the map.
\begin{spec}
%  op mapi : fa(key,a,b) (key -> a -> b) -> Map (key,a) -> Map (key,b)
%  op map : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
\end{spec}

The next applies a function to the entries of the map. It returns the
unit These functions make little sense in an applicative context. To be
of any use, the given function must have side-effects. These functions
should probably be omitted in the absence of a monad to encapsulate the
side-effects. In a monad, they can be combined with the functions above.
These functions are likely to disappear from this interface.

\begin{spec}
%  op appi : fa(key,a) (key -> a -> ()) -> Map (key,a) -> ()
%  op app : fa(key,a) (a -> ()) -> Map (key,a) -> ()
\end{spec}

I don't think that for abstract maps over unordered elements, folding
left or right should be distinguished. It is assumed below that the fold
is over all key / value pairs. The other folds in this signature are
apply only to the value and are a special case.

\begin{spec}
  op foldMap : fa(a) (a -> Dom -> Cod -> a) -> a -> Map -> a
%   op foldri : fa(b)  (Dom -> Cod -> b -> b) -> b -> Map -> b
%   op foldr : fa(b) (Cod -> b -> b) -> b -> Map -> b
%   op foldli : fa(key,a,b) (Dom -> Cod -> b -> b) -> b -> Map -> b
%   op foldl : fa(b) (Cod -> b -> b) -> b -> Map -> b
\end{spec}

Don't understand the next one.

\begin{spec}
%  op foldriDouble : fa(key1,key2,a,b) (key1 -> key2 -> a -> b -> b)
%       -> b -> Map (key1, Map (key2, a)) -> b
\end{spec}

Compose two maps. In the monomorphic case, this requires that
the domain and range be of the same type. Either that or we make two
copies of the Maps spec and derive a third.

\begin{spec}
%  op compose : fa(dom,med,rng) Map (dom,med) -> Map (med,rng) -> Map (dom,rng)
\end{spec}

\begin{spec}
  op unionWith : (Cod -> Cod -> Cod) -> Map -> Map -> Map
%  op unionWith : fa(key,a) (a -> a -> a)
%       -> Map (key,a) -> Map (key,a) -> Map (key,a)
%  op unionWithi : fa(key,a) (key -> a -> a -> a)
%       -> Map (key,a) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
%  op intersectWith : fa(key,a) (a -> a -> a)
%       -> Map (key,a) -> Map (key,a) -> Map(key,a)
%  op intersectWithi : fa(key,a) (key -> a -> a -> a)
%       -> Map (key,a) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
%  op filter  : fa(key,a) (a -> Bool) -> Map (key,a) -> Map (key,a)	  
%  op filteri : fa(key,a) (key -> a -> Bool) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
%  op mapPartial : fa(key,a,b) (a -> Option b)
%       -> Map (key,a) -> Map (key,b)
%  op compare : fa(a,key) (a * a -> Comparison)
%       -> Map (key,a) -> Map (key,a) -> Comparison
\end{spec}

Form a map from an association list. This should be generalized to
form a map from an association set.

\begin{spec}
%  op fromList : fa (a,b) (a * a -> Comparison)
%            -> List (a * b) -> Map (a, b)
\end{spec}

\begin{spec}
  op subset? : Map -> Map -> Bool
\end{spec}

\begin{spec}
  op all : (Dom -> Cod -> Bool) -> Map -> Bool
  op exists : (Dom -> Cod -> Bool) -> Map -> Bool
\end{spec}

Pretty printing. As in sets, it is not clear that this belongs in this
spec or in specific refinements of it. Note that the map is printed
in the reverse order to the way it it traversed by foldMap.

\begin{spec}
  op ppMap : Map -> WLPretty
  def ppMap map =
     ppSep ppNewline (foldMap (fn l -> fn dom -> fn cod
               -> Cons (ppConcat [
                          ppDom dom,
                          ppString " +-> ",
                          ppCod cod], l)) [] map)
}
\end{spec}
