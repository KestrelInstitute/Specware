\section{Polymorphic Maps}
A stripped down version of Polymorphic.


\begin{spec}
spec {
  sort Map (key,a)

  op emptyMap : fa(key,a) Map (key,a)

  op apply : fa(key,a) Map(key,a) * key -> Option a
  op eval  : fa(key,a) Map(key,a) * key -> a

  op update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
  op remove : fa (a,key) Map (key,a) * key -> Map (key,a)
\end{spec}

\begin{spec}
  op inDomain? : fa(key,a) Map (key,a) * key -> Boolean
  op numItems : fa(a,key) Map (key,a) -> Nat
\end{spec}

The functions that follow come in two varieties. All take functions
that operate on elements in the tree. For those with an `i' suffix, the
function is applied to both the key and the value. For those without
the `i' suffux, the supplied function is applied to only the values.

The next pair map a supplied function across the entries in the map.
\begin{spec}
  op mapi : fa(key,a,b) (key * a -> b) -> Map (key,a) -> Map (key,b)
  op map  : fa(key,a,b) (a -> b) -> Map (key,a) -> Map (key,b)
\end{spec}

Only useful with side-effects.
\begin{spec}
  op app   : fa(key,a) (a -> ()) -> Map (key,a) -> ()
  op appi  : fa(key,a) (key * a -> ()) -> Map (key,a) -> ()
\end{spec}


\begin{spec}
  op foldi : fa(Dom,Cod,a) (Dom * Cod * a -> a) -> a -> Map (Dom,Cod) -> a
\end{spec}

The next constructs the list elements from the range of the map
in ``order of appearance'' (with duplications). Order of appearance is 
meaningless unless an implementation is assumed.

\begin{spec}
  op imageToList : fa(key,a) Map (key,a) -> List a
\end{spec}

List the key/range pairs in order of appearance.

\begin{spec}
  op mapToList : fa(key,a) Map (key,a) -> List (key * a)
\end{spec}

\begin{spec}
  op domainToList : fa(key,a) Map (key,a) -> List key
\end{spec}

\begin{spec}
  op unionWith : fa(key,a) (a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
  op unionWithi : fa(key,a) (key * a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
  op intersectWith : fa(key,a) (a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map(key,a)
  op intersectWithi : fa(key,a) (key * a * a -> a)
       -> Map (key,a) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
  op filter  : fa(key,a) (a -> Boolean) -> Map (key,a) -> Map (key,a)	  
  op filteri : fa(key,a) (key * a -> Boolean) -> Map (key,a) -> Map (key,a)
\end{spec}

\begin{spec}
  op mapPartial  : fa(key,a,b) (a -> Option b) -> Map (key,a) -> Map (key,b)
  op mapiPartial : fa(key,a,b) (key * a -> Option b) -> Map (key,a) -> Map (key,b)
  op compare : fa(a,key) (a * a -> Comparison)
       -> Map (key,a) -> Map (key,a) -> Comparison
\end{spec}

\begin{spec}
  op submap? : fa (a,b) Map (a,b) * Map (a,b) -> Boolean
\end{spec}

\begin{spec}
  op allMap : fa (a,b) (a * b -> Boolean) -> Map (a,b) -> Boolean
  op existsMap : fa (a,b) (a * b -> Boolean) -> Map (a,b) -> Boolean
\end{spec}

\begin{spec}
}
\end{spec}
