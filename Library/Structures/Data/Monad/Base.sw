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

\begin{spec}
spec {
  sort Monad a

  op monadBind : fa (a,b) (Monad a) * (a -> Monad b) -> Monad b
  op monadSeq : fa (a,b) (Monad a) * (Monad b) -> Monad b
  op return : fa (a) a -> Monad a

  axiom left_unit is
    sort fa (a,b) fa (f:a->Monad b,x:a) monadBind (return x,f) = f x

  axiom right_unit is sort fa (a) fa (m:Monad a) monadBind (m,return) = m

  axiom associativity is
    sort fa (a,b,c) fa (m:Monad a, f:a ->Monad b, h:b->Monad c)
      monadBind (m,(fn x -> monadBind (f x, h))) = monadBind (monadBind (m,f), h)
\end{spec}

Can the above we written using the monadic syntax?

This next axiom could just as well be definition of the second
sequencing operator but that might preclude one from refining it.

\begin{spec}
axiom non_binding_sequence is
  sort fa (a) fa (f:Monad a,g:Monad a) monadSeq (f,g) = monadBind (f,fn _ -> g)
\end{spec}

The following is essentially a \verb+foldl+ over a list but within a
monad. We may want to change the order this function takes its arguments
and the structure of the argument (ie. curried or not) to be consistent
with other fold operations. (But they are in the order that I like :-).

These don't belong here .. there are specific to lists and
should be abstracted to data-types over which one can iterate.

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
