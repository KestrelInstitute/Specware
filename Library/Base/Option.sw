\section{Option}

To avoid, cyclic dependencies, the \verb|show| function for this
type is found in spec \verb|Show|.

\begin{spec}
Option qualifying spec
  sort Option a = | None | Some a
end
\end{spec}
