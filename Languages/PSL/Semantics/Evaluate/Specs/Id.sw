\section{Qualified Ids}

This defines the sort \verb+QualifiedId+ and
sets of such things. There is some inconsistency here
as usually the spec that uses sets creates it.

This should be enriched with constructors and destructors (projections).

As elsewhere, there may be a win in renaming \verb+make+ to \verb+makeId+.
Cast your vote. The references to \verb+String+ should probably be
made abstract.

\begin{spec}
Id qualifying spec
  import translate (Id qualifying /Library/Structures/Data/Sets/Monomorphic) by {
    Elem.Elem +-> Id.QualifiedId,
    Elem.pp +-> Id.pp
  }

  op make : String -> String -> QualifiedId
  op UnQualifiedId.make : String -> QualifiedId

  op pp : QualifiedId -> Doc
endspec
\end{spec}
