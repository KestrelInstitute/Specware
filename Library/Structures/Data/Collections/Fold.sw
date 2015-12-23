(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Commutative Fold}

This is a variation but weaker characterization of fold taught to me by Alessandro.

His is writen for \Spec{Sets} and is tighter as he requires only that
the folded operation commute only over the elements of the set to which
it is applied. Here, the folded operation commutes over the entire type.

His version requires an uncurried type for \Op{fold} as the domain is given
by a subtype. This isn't possible for the curried version unless we have
dependent types.

\begin{spec}
spec
  import Enum

  op foldable? : fa (a) (a * Elem -> a) -> Bool
  type Foldable a = ((a * Elem -> a) | foldable?) 

  op fold : fa (a) Foldable a * a * Collection -> a 

  % axiom foldable is fa (f) (foldable? f) <=> (fa (x,y,z) f (f x y) z = f (f x z) y)
  % axiom fold_unit is fa (c,f) fold f c empty = c 
  % axiom fold_iteration is fa (s,x,c,f) fold f c (s with x) = fold f (f c x) (s without x)
endspec
\end{spec}

Not sure how to make sense of Alessandro's axioms for types other than \Type{Set}.
