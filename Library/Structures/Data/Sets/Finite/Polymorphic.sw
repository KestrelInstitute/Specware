(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Basic polymorphic sets}

This should be formed by composition of simpler specifications for
polymorphic collections.

\begin{spec}
spec
  type Set a

  op empty        : fa (a) Set a
  op empty?       : fa (a) Set a -> Bool
  op size         : fa (a) Set a -> Nat
  op union        : fa (a) Set a * Set a -> Set a
  op intersect    : fa (a) Set a * Set a -> Set a
  op difference   : fa (a) Set a * Set a -> Set a
  op member?      : fa (a) Set a * a     -> Bool
  op subset?      : fa (a) Set a * Set a -> Bool
  op delete       : fa (a) Set a * a -> Set a
  op singleton    : fa (a) a         -> Set a
  op insert       : fa (a) Set a * a -> Set a
  op theSingleton : fa (a) (Set a | fn set -> ex (x) set = singleton x) -> a
endspec
\end{spec}
