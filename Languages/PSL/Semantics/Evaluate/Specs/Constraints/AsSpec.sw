\section{Simple refinements of substutions as \Sort{OpInfo}}

The idea here is that we can apply a substitution to a spec by simply
merging the substitution spec with the given spec.

\begin{spec}
Constraints qualifying spec 
  import ../Constraints

  sort Constraints.Constraints = Spec.Spec
endspec
\end{spec}
