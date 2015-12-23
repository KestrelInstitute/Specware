(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Finite Collections}

Any finite collection is enumerable. If it is finite we believe that it can
be printed.

\begin{spec}
spec
  import Enum
  import Fold
  import FoldLeft
  import FoldRight
  
  op size : Collection -> Nat

  op pp : Collection -> Doc
  op show : Collection -> String
endspec
\end{spec}
