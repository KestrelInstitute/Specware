\section{Monomorphic Sets}

This is a spec for basic monomorphic sets.  The axioms have been omitted
for the time being as have many of the useful operations.  This is the
way that sets might have been defined in the old Slang.

\begin{spec}
spec
  % import /Library/PrettyPrinter/WadlerLindig
  import Elem

  sort Set

  op empty : Set
  op empty? : Set -> Boolean

  op union : Set -> Set -> Set
  op intersection : Set -> Set -> Set
  op difference : Set -> Set -> Set

  op member? : Set -> Elem -> Boolean
  op delete : Set -> Elem -> Set

  op singleton : Elem -> Set
  op insert : Set -> Elem -> Set

  op fold : fa(a) (a -> Elem -> a) -> a -> Set -> a
  op map : (Elem -> Elem) -> Set -> Set
\end{spec}

This pretty prints the elements of a list with breaks at each element.
This needs a rethink. Perhaps we should be able to print the elements
of the list on a line and specify the separator.

Also it is not clear that a concrete definition belongs here at all.
Perhaps it belongs in the refinements of this spec.

\begin{spec}
  op ppSet : Set -> Pretty
  def ppSet set =
     ppSep (ppString ",")
       (fold (fn l -> fn elem -> Cons (ppElem elem, l)) [] set)
\end{spec}

These don't belong here
\begin{spec}
  op toList : Set -> List Elem
%  op addList : Set -> List Elem -> Set
%  op fromList : List Elem -> Set
end
\end{spec}

Intuitively, when \sortref{Set} = \sortref{List} then,

\begin{verbatim}
   fold f e [] = e
   fold f e (h:t) = f h (fold e t)
\end{verbatim}

One could argue that fold does not belong in this spec since it assumes
the elements of the set are finitely enumerable. Perhaps there should be
a more abstract spec where the operator is omitted and a refinement
for enumerable sets where fold is included.

One could also argue that the last three don't belong in this spec.

A problem with the presentation is that, as I see it, the dependency
between the sort Set and the sort Elem is not reflected in the definition
of the sort Set. Put another way, the sort for Set, does not say
explicitly that it is a sort for sets of Elem.
