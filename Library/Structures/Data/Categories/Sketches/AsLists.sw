\section{Naive refinement of sketches}

This must import the refined spec for graphs and translate it in the
same was a ../Sketches.sw

\begin{spec}
spec
  import translate ../../Graphs/Finite/AsLists by {Graph +-> Sketch}
  import ../Sketches
endspec
\end{spec}
