\section{Exception monad}

An abstract specification for an exception monad. Needs work.
What are the axioms?

\begin{spec}
spec {
  import Base

  sort Exception

  op throw : fa (a) Exception -> Monad a
  op catch : fa (a) Monad a -> (Exception -> Monad a) -> Monad a
}
