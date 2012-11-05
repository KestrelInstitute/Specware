\section{Iteration within a monad}

The first function a \verb+fold+ over any finite and enumerable
data type but within a monad.

\begin{spec}
spec
  import ../Finite
  import ../Monad

  op fold : fa (a) (a -> Elem -> Monad a) -> a -> Collection -> Monad a
  def fold f a l =
    case (takeOne l) of
      | None -> return a
      | One (x,xs) -> {
            y <- f a x;
            fold f y xs
          }
\end{spec}

Analogously, this is the monadic version of \verb+map+. This works
but is specific to mapping over a list. It has been omitted (hence
the verbatim environment). To generalize this as above
requires constuctors associated with the Enumerable type.

\begin{verbatim}
  op map : fa (a,b) (a -> Monad b) -> (List a) -> Monad (List b)
  def map f l =
    case l of
      | [] -> return []
      | x::xs -> {
            xNew <- f x;
            xsNew <- map f xs;
            return (Cons (xNew,xsNew))
          }
\end{verbatim}

\begin{spec}
endspec
\end{spec}
