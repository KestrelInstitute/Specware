\section{Evalution of a term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import ../Environment

  sort SCTerm = SpecCalc.Term Position

  op evaluateTerm        : SCTerm                                             -> Env Value

  op evaluateLet         : List (Decl Position) -> SCTerm                     -> Env ValueInfo

  op evaluateURI         : Position -> RelativeURI                            -> Env ValueInfo
  op evaluateSpec        : List (SpecElem Position)                           -> Env ValueInfo
  op evaluateSpecMorph   : SCTerm * SCTerm * (List (SpecMorphRule Position))  -> Env ValueInfo
  op evaluateLispCompile : ValueInfo * SCTerm * Option String                 -> Env ValueInfo
  op evaluateDiag        : List (DiagElem Position)                           -> Env ValueInfo
  op evaluateDiagMorph   : SCTerm * SCTerm * (List (DiagMorphRule Position))  -> Env ValueInfo
  op evaluateColimit     : SCTerm                                             -> Env ValueInfo
  op evaluateTermInfo    : SCTerm                                             -> Env ValueInfo
  op evaluatePrint       : SCTerm                                             -> Env ValueInfo
  op evaluateQualify     : SCTerm -> Qualifier                                -> Env ValueInfo
  op evaluateTranslate   : SCTerm -> TranslateExpr Position                   -> Env ValueInfo
  op evaluateSubstitute  : SCTerm * SCTerm                       -> Position  -> Env ValueInfo
  op evaluateObligations : SCTerm                                             -> Env ValueInfo

  op getURI : SCTerm -> Env URI

}
\end{spec}
