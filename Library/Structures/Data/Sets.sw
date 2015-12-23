(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Monomorphic Sets}

This is a spec for basic monomorphic sets.  The axioms have been omitted
for the time being as have many of the useful operations.  This is the
way that sets might have been defined in the old Slang.

\begin{spec}
spec
  import translate Collections by {Collection +-> Set}

  op empty        : Set
  op empty?       : Set -> Bool
  op member?      : Set * Elem -> Bool
  op union        : Set * Set  -> Set
  op intersection : Set * Set  -> Set
  op difference   : Set * Set  -> Set
  op delete       : Set * Elem -> Set
  op singleton    : Elem       -> Set
  op insert       : Set * Elem -> Set
  op theSingleton : (Set | fn set -> ex (x) set = singleton x) -> Elem
endspec
\end{spec}
