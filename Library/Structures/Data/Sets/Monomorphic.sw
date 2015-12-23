(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Monomorphic Sets}

This is in use but to be deprecated. Use ../Sets.sw instead

This is a spec for basic monomorphic sets.  The axioms have been omitted
for the time being as have many of the useful operations.  This is the
way that sets might have been defined in the old Slang.

\begin{spec}
spec
  import Elem 

  type Set

  op empty        : Set
  op empty?       : Set -> Bool
  op member?      : Set -> Elem -> Bool
  op subset?      : Set -> Set  -> Bool
  op delete       : Set -> Elem -> Set
  op insert       : Set -> Elem -> Set
  op union        : Set -> Set -> Set
  op intersection : Set -> Set -> Set
  op difference   : Set -> Set -> Set
  op singleton    : Elem       -> Set

  % These belong in some extended spec for finite or enumerable sets. 
  op fold    : fa(a) (a -> Elem -> a) -> a -> Set -> a
  op map     : (Elem -> Elem) -> Set -> Set
 %op takeOne : Set -> Option (Elem * Set)
\end{spec}

This pretty prints the elements of a list with breaks at each element.
This needs a rethink. Perhaps we should be able to print the elements
of the list on a line and specify the separator.

Also it is not clear that a concrete definition belongs here at all.
Perhaps it belongs in the refinements of this spec.

\begin{spec}
  op pp : Set -> WLPretty
  def pp set =
     ppSep (ppString ",")
       (fold (fn l -> fn elem -> Cons (Elem.pp elem, l)) [] set)
\end{spec}

These don't belong here

\begin{spec}
  op toList : Set -> List Elem
%  op addList : Set -> List Elem -> Set
%  op fromList : List Elem -> Set
end-spec
\end{spec}

Intuitively, when \typeref{Set} = \typeref{List} then,

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
between the type Set and the type Elem is not reflected in the definition
of the type Set. Put another way, the type for Set, does not say
explicitly that it is a type for sets of Elem.
