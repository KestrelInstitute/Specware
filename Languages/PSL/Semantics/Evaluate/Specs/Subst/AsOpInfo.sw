\section{Simple refinements of substutions as \Sort{OpInfo}}

The idea here is that we can apply a substitution to a spec by simply
adding the \Sort{OpInfo}s associated with the name to the spec. The
step of acually performing the reductions is done elsewhere.

So we can substitute only for ops and not variables using this scheme.
But the distinction between ops and variables is wrong in the first place.

\begin{spec}
Subst qualifying spec 
  import ../Subst
  import ../Op/Legacy
  import ../Spec/Legacy

  sort Subst.Subst = List Op.OpInfo
  def Subst.pp subst =
    ppConcat [
        String.pp "[",
        ppSep (String.pp ",") (map ppShort subst),
        String.pp "]"
      ]
  def Subst.show subst = ppFormat (pp subst)

  def Subst.equalSubst? (s1,s2) = equalList? (s1,s2,equalOpInfo?)
endspec
\end{spec}
