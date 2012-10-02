\section{Recording type, operator and spec history}

Want to have traces of how an op type or axiom comes into being.

This following is not essential for the near term.

To assist a user debugging a spec containing many layers of import and non-trivial
use of qualifiers, it would be useful to record how an op, for example, came
to be in a spec. 

Below, the history is a list of actions. A list may not be sufficient
as the same op may be imported many times.

\begin{spec}
  type History = List Action

  type Action =
      | Declared Position
      | Translate (QualifiedId * Position)
      % | Substitute ...
      | Qualified (String * Position)
      % | Imported (SCTerm * Position)

  op Op.history : OpInfo -> History
  op Type.history : TypeInfo -> History
\end{spec}

To support recording the history, the operations that
transform the spec must be extended.

\begin{spec}
  type Translation
  op Op.translate : Spec -> Translation -> OpInfo -> Spec
  op Type.translate : Spec -> Translation -> TypeInfo -> Spec
\end{spec}

Many people have suggested that we record the spec calculus terms that a
spec imports.  Right now we record strings rather than the terms which
has questionable value.  Recording the term wasn't done, in part because
there was no obvious use, and because of the recusion between the types
\verb+Spec+ and \verb+SCTerm+. Thes live in two different specs. In fact
the mutual recursion is possible
but the loop must be closed by refinement.
