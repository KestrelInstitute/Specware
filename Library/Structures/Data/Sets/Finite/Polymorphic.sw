\section{Basic polymorphic sets}

This should be formed by composition of simpler specifications for
polymorphic collections.

\begin{spec}
spec
  sort Set a

  op empty : fa(a) Set a
  op empty? : fa (a) Set a -> Boolean

  op union : fa(a) Set a * Set a -> Set a
  op intersect : fa (a) Set a * Set a -> Set a
  op difference : fa (a) Set a * Set a -> Set a

  op member? : fa(a) Set a * a -> Boolean
  op delete : fa(a) Set a * a -> Set a

  op singleton : fa (a) a -> Set a
  op theSingleton : fa(a) (Set a | fn set -> ex (x) set = singleton x) -> a

  op insert : fa (a) Set a * a -> Set a
  op size : fa (a) Set a -> Nat
endspec
\end{spec}
