\section{Iteration within a monad}

The first function a \verb+fold+ over any finite and enumerable
data type but within a monad.

### This definition wrongly constrains the collection sort to
be enumerable. The point is that there is no reason that the
fold operation should be expressed in terms if takeOne. By doing
so we are implicitly asserting that the order of the fold is relevant.


\begin{spec}
spec
  import ../Finite
  import translate ../Enum by {
      Enum.Collection +-> Collection,
      Enum.takeOne +-> takeOne,
      Enum.TakeResult +-> TakeResult
    }
   
  import ../Monad

  op fold : fa (a) (a -> Elem -> Monad a) -> a -> Collection -> Monad a
  def fold f a l =
    case (takeOne l) of
      | None -> return a
      | One (x,xs) -> {
            y <- f a x;
            fold f y xs
          }
endspec
\end{spec}
