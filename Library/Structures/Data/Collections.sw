\section{Collections}

Meant to be an abstraction of Sets, Maps, Bags etc. These are things that
have enough structure to support a canonical lifting of an operation on
a sort to a function over a collection of things of that sort.

This is not well thought out at this stage. Work in progress.

In fact, this is silly. Need two collections to properly define \Op{map}

\begin{spec}
spec
  import Elem qualifying Elem

  sort Collection

  % op map : (Elem -> Elem) -> Collection -> Collection
endspec
\end{spec}
