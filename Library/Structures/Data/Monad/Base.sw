\section{Basic Monad Specification}

All Monad specs refine or extend this specification.

This is not used at present.

This raises the issue of naming specs. We would like to call
this Structures/Data/Monad but this will clutter the parent directory
with base specs for all sorts of things. It is typical when a
url is resolved that a name like /a/b actually leads to a file
like .../a/b/index.html. Perhaps we should to the same so that
Structures/Data/Monad resolves to Structures/Data/Monad/Base.sw

This defines both the prefix and infix operators. There is
support for the prefix form in the MetaSlang parser.

spec {
  sort Monad a

  op monadBind : fa (a,b) (Monad a) * (a -> Monad b) -> Monad b
  op monadSeq : fa (a,b) (Monad a) * (Monad b) -> Monad b
  op return : fa (a) a -> Monad a

  op >>= infixl 6 : fa (a,b) Monad a * (a -> Monad b) -> Monad b
  op >> infixl 6 : fa (a,b) Monad a * Monad b -> Monad b

  axiom "left unit" is
    sort fa (a,b) fa (f : a -> Monad b, x : a) ((return x) >>= f) = (f x)

  axiom "right unit" is sort fa (a) fa (m : Monad a) (m >>= return) = m

  axiom "associativity" is
    sort fa (a,b,c) fa (m : Monad a, f : a -> Monad b, h : b -> Monad c)
      (m >>= (fn x -> (f x >>= h))) = ((m >>= f) >>= h)
\end{spec}

This next axiom could just as well be definition of the second
sequencing operator but that would preclude one from refining it.

\begin{spec}
  axiom "non-binding sequence" is
    sort fa (a) fa (f : Monad a, g : Monad a) (f >> g) = (f >>= (fn _ -> g))
\end{spec}

The following is essentially a \verb+foldl+ over a list but within a
monad. We may want to change the order this function takes its arguments
and the structure of the argument (ie. curried or not) to be consistent
with other fold operations. (But they are in the order that I like :-).

Perhaps these don't belong here .. as we can probably abstract
the sort List to any type we can iterate over.

\begin{spec}
  op fold : fa (a,b) (a -> b -> Monad a) -> a -> List b -> Monad a
  def fold f a l =
    case l of
      | [] -> return a
      | x::xs -> {
            y <- f a x;
            fold f y xs
          }
\end{spec}

Analogously, this is the monadic version of \verb+map+. 

\begin{spec}
  op map : fa (a,b) (a -> Monad b) -> (List a) -> Monad (List b)
  def map f l =
    case l of
      | [] -> return []
      | x::xs -> {
            xNew <- f x;
            xsNew <- map f xs;
            return (Cons (xNew,xsNew))
          }
}
\end{spec}
