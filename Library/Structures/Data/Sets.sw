\section{Monomorphic Sets}

This is a spec for basic monomorphic sets.  The axioms have been omitted
for the time being as have many of the useful operations.  This is the
way that sets might have been defined in the old Slang.

\begin{spec}
spec
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

  op map : (Elem -> Elem) -> Set -> Set
endspec
\end{spec}
