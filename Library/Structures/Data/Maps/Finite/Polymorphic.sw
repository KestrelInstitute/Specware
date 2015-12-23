(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Simple Polymorphic Maps as Lists}

This should come about by composition of polymorphic collections etc.

\begin{spec}
Map qualifying spec
  type Map (key,a) = List (key * a)

  op empty : fa(key,a) Map (key,a)

  (*
   * evalPartial may disappear when the library is restructured
   * with separate directories for total and partial maps.
   *)
  op evalPartial : fa(key,a) Map (key,a) * key -> Option a
  op eval : fa(key,a) Map (key,a) * key -> a
  op update : fa (key,a) Map (key,a) * key * a -> Map (key,a)
endspec
\end{spec}
