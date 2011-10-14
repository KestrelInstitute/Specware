\section{Monadic Sets}

This is an instance of monomorphic sets extended with monadic fold operation
over the set.

The monadic types and ops are all qualified with \Qualifier{SpecCalc}.

\begin{spec}
let Monad = /Library/Structures/Data/Monad/Fold in
spec
  import translate (translate Monad
    by {Collection +-> Set, Monad.Monad +-> SpecCalc.Env})
    by {Monad._ +-> SpecCalc._}
  import /Library/Structures/Data/Sets/Finite
endspec
\end{spec}
