\section{Naive refinement of sketches}

This must import the refined spec for graphs and translate it in the
same was a ../Sketches.sw

\begin{spec}
spec
  import translate ../Graphs/AsLists by {Graph +-> Sketch}
  import /Library/Structures/Data/Categories/Sketches
endspec
\end{spec}
