\section{Abstract Morphisms}

Not used at present.

Questionable value. Need to use subtyping to get compose correct
in which case it shouldn't be curried.

The idea is to put in here (once) the axioms for morphism composition.

An explicit sort for Objects may seem odd give the O type variables,
but imagine constucting a functor category over a given category. In
this case the O and A refer to the underlying cat.

\begin{spec}
spec {
  sort Object (O,A)
  sort Morphism (O,A)

  op dom : fa (O,A) Morphism (O,A) -> Object (O,A) 
  op cod : fa (O,A) Morphism (O,A) -> Object (O,A)

  op compose : fa (O,A) Morphism (O,A) -> Morphism (O,A) -> Morphism (O,A)
}
\end{spec}

