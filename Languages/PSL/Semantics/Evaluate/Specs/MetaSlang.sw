\section{Abstraction of MetaSlang Terms}

Not clear that this is useful at this stage. Would
prefer the qualifier to be MetaSlang but this is taken.

It is expected that \Sort{Term} refines to \Sort{ATerm Position}
Similary, we expect that \Sort{Type} refines to \Sort{ASortScheme Position}

\begin{spec}
MS qualifying spec
  import Pretty

  sort Position
  sort Term
  sort Type
  sort TypeVars

  op Term.pp : Term -> Doc
  op Term.show : Term -> String

  op Type.pp : Type -> Doc
  op Type.show : Type -> String
endspec
\end{spec}
