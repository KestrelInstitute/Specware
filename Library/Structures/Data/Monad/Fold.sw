(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Iteration within a monad}

The first function a \verb+fold+ over any finite and enumerable
data type but within a monad.

### This definition wrongly constrains the collection type to
be enumerable. The point is that there is no reason that the
fold operation should be expressed in terms if takeOne. By doing
so we are implicitly asserting that the order of the fold is relevant.

Need axioms for commutativity.

Does \Op{foldr} have any use?

The definitions don't belong here.

### There is a bug here. If we qualify the following spec with Monad we
the fold operations in finite Collections disappear. It should cause
an error.

\begin{spec}
spec
  import ../Collections/Finite
  import ../Monad

  op MonadFold.foldl : fa (a) (a -> Elem -> Monad a) -> a -> Collection -> Monad a
  def MonadFold.foldl f a l =
    case (takeOne l) of
      | None -> return a
      | One (x,xs) -> {
            y <- f a x;
            foldl f y xs
          }

  op MonadFold.foldr : fa (a) (a -> Elem -> Monad a) -> a -> Collection -> Monad a
  def MonadFold.foldr f a l =
    case (takeOne l) of
      | None -> return a
      | One (x,xs) -> {
            y <- foldr f a xs;
            f y x
          }

  op MonadFold.fold : fa (a) (a -> Elem -> Monad a) -> a -> Collection -> Monad a
endspec
\end{spec}
