\section{Basic Monad Specification}

All monad specs refine or extend this specification.

This defines just the prefix operators. There is support in the MetaSlang
grammar to generate these functions.

\begin{spec}
Monad qualifying spec
  sort Monad a

  op monadBind : fa (a,b) (Monad a) * (a -> Monad b) -> Monad b
  op monadSeq : fa (a,b) (Monad a) * (Monad b) -> Monad b
  op return : fa (a) a -> Monad a

  axiom left_unit is
    sort fa (a,b) fa (f:a-> Monad b,x:a) monadBind (return x,f) = f x

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
endspec
\end{spec}
