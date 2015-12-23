(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Basic Monad Specification}

This location is deprecated.

The issue is where to place specs. The problem with
Structures/Data/Monad.sw is that it clutters the parent directory
with base specs for all types of things. It is typical when a
url is resolved that a name like /a/b actually leads to a file
like .../a/b/index.html. Perhaps we should to the same so that
Structures/Data/Monad resolves to Structures/Data/Monad/Base.sw

This defines both the prefix and infix operators. There is
support for the prefix form in the MetaSlang parser.

\begin{spec}
translate ../Monad by {Monad._ +-> _}
\end{spec}
