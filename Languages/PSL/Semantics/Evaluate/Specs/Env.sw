\section{The Specware Environment Monad}

We need support for exceptions and state (and later perhaps IO).

\begin{spec}
let Monad =
  spec
    import /Library/Structures/Data/Monad/Exception
    import /Library/Structures/Data/Monad/State
  endspec
in spec
  import translate (translate Monad by {Monad.Monad +-> Env.Env}) by {Monad._ +-> Env._}
endspec
\end{spec}
