\section{Exception monad}

An abstract specification for an exception monad. Needs work.
What are the axioms?

\begin{spec}
spec {
  import Base

  sort Exception

  op raise : fa (a) Exception -> Monad a
  op throw : fa (a) Exception -> Monad a
  op catch : fa (a) Monad a -> (Exception -> Monad a) -> Monad a

  axiom throw_is_raise is throw = raise
}
