\section{Monadic Sets}

The point of all this is just to instantiate the sort
for the monadic fold operations. We have to translate the monad
names in the same way as in \UnitId{Env}

\begin{spec}
let Monad = /Library/Structures/Data/Monad/Fold in
spec
  import translate (translate Monad by {Collection +-> Set, Monad.Monad +-> Env.Env}) by {Monad._ +-> Env._}
  import /Library/Structures/Data/Sets/Finite
endspec
\end{spec}
