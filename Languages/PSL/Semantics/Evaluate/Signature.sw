\section{Evalution of a term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../Environment

  sort SCTerm = SpecCalc.Term Position

  %% Generic mechanism:

  op evaluateTerm        : SCTerm                                             -> Env Value
  op evaluateLet         : List (Decl Position) -> SCTerm                     -> Env ValueInfo

  %% Specific kinds of terms:

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
  op evaluatePSpec       : List (PSpecElem Position)                          -> Env ValueInfo

  %% Lower-level support routines:

  op getURI : SCTerm -> Env URI
  op coerceToSpec : Value -> Value
}
\end{spec}
