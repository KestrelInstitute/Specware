\section{Basic spec for polymorphic sets}

Basic spec for polymorphic sets. Again, there are no axioms at this point.

\begin{spec}
spec
  import /Library/PrettyPrinter/WadlerLindig

  sort Set a

  op empty : [a] Set a
  op empty? : [a] Set a -> Boolean

  op union : [a] Set a -> Set a -> Set a
  op intersection : [a] Set a -> Set a -> Set a
  op difference : [a] Set a -> Set a -> Set a

  op member? : [a] Set a -> a -> Boolean
  op subset?: [a] Set a -> Set a -> Boolean

  op delete : [a] Set a -> a -> Set a
  op insert : [a] Set a -> a -> Set a

  op find: [a] (a -> Boolean) -> Set a -> Option a

  op singleton : [a] a -> Set a

  % op fold : fa (a) (a -> a -> a) -> a -> Set a -> a

  op fold : [a,b] (a -> b -> a) -> a -> Set b -> a
  op map  : [a,b] (a -> b) -> Set a -> Set b

  % op takeOne : fa (a) Set a -> Option (a * Set a)

  op ppSet : [a] (a -> Pretty) -> Set a -> Pretty
\end{spec}

The operator \verb+take+ will remove an arbitrary element
from a list and return the element and the new list. If the
list is empty it yields \verb+None+.

These shouldn't be here.

\begin{spec}
  op toList : [a] Set a -> List a
  op fromList : [a] List a -> Set a
%  op addList : [a] Set a -> List a -> Set a
end
\end{spec}

One could argue that monomorphic sets can be obtained as an instance of
the polymorphic by something like the following:

\begin{verbatim}
spec 
  import PolySets
  sort Elem
  sort Set' = Set Elem
end
\end{verbatim}

But, of course, this doesn't quite work. It defines a new sort, Set',
instead of refining the imported sort, Set. To do the instantiation
properly and uniformly across all the operators, it would seem that one
would need to be possible to parameterize specs on sorts.
