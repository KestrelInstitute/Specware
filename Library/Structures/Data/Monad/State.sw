\section{State monad}

A simple state monad. Needs work.
What are the axioms?

\begin{spec}
Monad qualifying spec
  import ../Monad
  import Exception

  sort Var
  sort Value

  op readVar : Var -> Monad Value
  op writeVar : Var -> Value -> Monad ()
endspec
