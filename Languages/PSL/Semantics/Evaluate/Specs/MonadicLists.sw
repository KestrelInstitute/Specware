\section{Monadic Sets}

Fold over a polymorphic list inside a monad.

\begin{spec}
spec
  import translate (translate /Library/Structures/Data/Monad by {Monad.Monad +-> SpecCalc.Env}) by {Monad._ +-> SpecCalc._}

  op MonadEnv.fold : fa (a,b) (a -> b -> Env a) -> a -> List b -> Env a
  def MonadEnv.fold f a l =
    case l of
      | [] -> return a
      | x::xs -> {
            y <- f a x;
            MonadEnv.fold f y xs
          }
endspec
\end{spec}
