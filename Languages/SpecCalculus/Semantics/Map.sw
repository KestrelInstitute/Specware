\section{Naive maps for the environment}

Derived from r1.2 SW4/Languages/SpecCalculus/Semantics/Map.sl

This will be removed from here. 

This will eventually go in
\url{Library/Structures/Data/Maps/Partial/Polymorphic} or something
like that.

We might be better to use monadic maps so that when you fail to find
an element you raise an exception rather than return the \verb+Some+
constructor.

This was meant to go into the spec library and hence conformance
with the map signatures defined in data-structures was not considered
important. I suppose we should decide what we want the libraries to
be and then gradually adjust the core to suit.

This ops below are fully curried. This is in part because I don't like
brackets .. but also because I find that knowing that everything is
curried is more convenient than when some arguments are curried
and some not. It is also more convenient when using higher-order functions.
Alessandro has pointed out, however, that currying precludes the use
of subsorts on the domain of a function. 

Needs thought.

The names emptyMap and foldMap might now revert to being unsuffixed.

The signature below is rather bloated. It is derived from the
splay map interface. It should be pruned and refactored.

\begin{spec}
Map qualifying spec {
  import /Library/PrettyPrinter/WadlerLindig

  sort Map (key,a)

  op emptyMap : fa(key,a) Map (key,a)

  op eval : fa(key,a) Map(key,a) -> key -> Option a

  op update : fa (key,a) Map (key,a) -> key -> a -> Map (key,a)
  op remove : fa (a,key) Map (key,a) -> key -> Map (key,a)
\end{spec}

Ultra naive implementation in terms of lists

\begin{spec}
  sort Map (key,a) = List (key * a)

  def emptyMap = Nil

  % ### op eval : fa(key,a) Map(key,a) -> key -> Option a
  def eval map x = 
    case map of
        [] -> None
      | (y,val)::tl -> 
           if x = y then
             (Some val)
           else
             eval tl x

  % ### op update : fa (key,a) Map (key,a) -> key -> a -> Map (key,a)
  def update map x y =
    case map of
        [] -> [(x,y)]
      | (u,v)::tl ->
          if (x = u) then
            Cons ((x,y),tl)
          else
            Cons ((u,v), update tl x y)

  def remove map x =
    case map of
        [] -> []
      | (u,v)::tl ->
          if x = u then tl
          else
            Cons ((u,v), remove tl x)

  op foldMap : fa(Dom,Cod,a) (a -> Dom -> Cod -> a) -> a -> Map (Dom,Cod) -> a
  def foldMap f z map =
    case map of
        [] -> z
      | (x,y)::tl -> foldMap f (f z x y) tl
\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

\begin{spec}
  % op image : fa (key,a) Map (key,a) -> Set a
  op imageToList : fa(key,a) Map (key,a) -> List a
\end{spec}

List the key/range pairs in order of appearance.

\begin{spec}
  op mapToList : fa(key,a) Map (key,a) -> List (key * a)
\end{spec}

\begin{spec}
  % op domain : fa(key,a) Map (key,a) -> Set key
  op domainToList : fa(key,a) Map (key,a) -> List key
\end{spec}

\begin{spec}
  op inDomain? : fa(key,a) Map (key,a) -> key -> Boolean
  op numItems : fa(a,key) Map (key,a) -> Nat
\end{spec}

The functions that follow come in two varieties. All take functions
that operate on elements in the tree. For those with an `i' suffix, the
function is applied to both the key and the value. For those without
the `i' suffux, the supplied function is applied to only the values.

The next pair map a supplied function across the entries in the map.
\begin{spec}
  op mapi : fa(key,a,b) (key -> a -> b) -> Map (key,a) -> Map (key,b)
  op mapMap : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
\end{spec}

\begin{spec}
  op foldMap : fa(Dom,Cod,a) (a -> Dom -> Cod -> a) -> a -> Map (Dom,Cod) -> a
  % op foldri : fa(key,a,b)  (key -> a -> b -> b) -> b -> Map (key,a) -> b
  % op foldr : fa(key,a,b) (a -> b -> b) -> b -> Map (key,a) -> b
  % op foldli : fa(key,a,b) (key -> a -> b -> b) -> b -> Map (key,a) -> b
  % op foldl : fa(key,a,b) (a -> b -> b) -> b -> Map (key,a) -> b
\end{spec}

Don't understand the next one.

\begin{spec}
  op foldriDouble : fa(key1,key2,a,b) (key1 -> key2 -> a -> b -> b)
       -> b -> Map (key1, Map (key2, a)) -> b
\end{spec}

Compose two maps. (compose f g = f;g). Perhaps it should be the other
way around.

\begin{spec}
  op compose : fa(dom,med,rng) Map (dom,med) -> Map (med,rng) -> Map (dom,rng)
\end{spec}

\begin{spec}
  op unionWith : fa(key,a) (a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
  op unionWithi : fa(key,a) (key -> a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
  op intersectWith : fa(key,a) (a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map(key,a)
  op intersectWithi : fa(key,a) (key -> a -> a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
  op filter  : fa(key,a) (a -> Boolean) -> Map (key,a) -> Map (key,a)	  
  op filteri : fa(key,a) (key -> a -> Boolean) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
  op mapPartial : fa(key,a,b) (a -> Option b) -> Map (key,a) -> Map (key,b)
  op compare : fa(a,key) (a * a -> Comparison)
       -> Map (key,a) -> Map (key,a) -> Comparison
\end{spec}

Form a map from an association sets and lists. 

\begin{spec}
  % op fromSet : fa (a,b) Set (a * b) -> Map (a, b)
  op fromList : fa (a,b) List (a * b) -> Map (a, b)
\end{spec}

\begin{spec}
  op subset? : fa (a,b) Map (a,b) -> Map (a,b) -> Boolean
\end{spec}

\begin{spec}
  op all : fa (a,b) (a -> b -> Boolean) -> Map (a,b) -> Boolean
  op exists : fa (a,b) (a -> b -> Boolean) -> Map (a,b) -> Boolean
\end{spec}

Pretty printing. As in sets, it is not clear that this belongs in this
spec or in specific refinements of it. Note that the map is printed
in the reverse order to the way it it traversed by foldMap.

\begin{spec}
  op ppMap : fa (a,b) (a -> Doc) -> (b -> Doc) -> Map (a,b) -> Doc
  def ppMap ppKey ppValue map =
     ppSep ppNewline (foldMap (fn l -> fn dom -> fn cod
               -> Cons (ppConcat [
                          ppKey dom,
                          ppString " |-> ",
                          ppValue cod], l)) [] map)
\end{spec}

\begin{spec}
}
\end{spec}
