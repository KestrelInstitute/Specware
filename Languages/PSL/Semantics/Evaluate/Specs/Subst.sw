\section{Substitutions}

This is experimental. This is used only by the partial evaluator.

Right now, this can't even define how to apply a substitution since that
is specific to the sort of spec or term to which it is applied. Needs thought.

But should we apply substitutions to specs and terms or only terms?

Really not clear where this belong? As part of Term?

\begin{spec}
Subst qualifying spec 
  import Id            % Not used at present.
  import Spec          % Not used at present.

  sort Subst
  sort Binding

  op pp : Subst -> Doc
  op show : Subst -> String

  op equalSubst? : Subst * Subst -> Boolean
  op Subst.eq? : Subst * Subst -> Boolean

  op filter : (Binding -> Boolean) -> Subst -> Subst

  op order : Subst -> Subst
endspec
\end{spec}
