\section{Evalution of a term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import ../Environment

  op evaluateURI : Position -> RelativeURI -> Env ValueInfo

  op getURI : SpecCalc.Term Position -> Env URI

  op evaluateSpec : List (SpecElem Position) -> Env ValueInfo

  op evaluateSpecMorph :
      (SpecCalc.Term Position) 
    * (SpecCalc.Term Position)
    * (List (SpecMorphElem Position))
    -> Env ValueInfo

  op evaluateDiag : List (DiagElem Position) -> Env ValueInfo

  op evaluateColimit : SpecCalc.Term Position -> Env ValueInfo

  op evaluateDiagMorph :
      (SpecCalc.Term Position)
    * (SpecCalc.Term Position)
    * (List (DiagMorphElem Position))
    -> Env ValueInfo

  op evaluateLispCompile : ValueInfo * SpecCalc.Term Position * Option String
			  -> Env ValueInfo

  op evaluateTerm : SpecCalc.Term Position -> Env Value

  op evaluateTermInfo : SpecCalc.Term Position -> Env ValueInfo

  op evaluatePrint : SpecCalc.Term Position -> Env ValueInfo

  op evaluateLet :
       List (Decl Position)
    -> SpecCalc.Term Position
    -> Env ValueInfo

  op evaluateQualify : SpecCalc.Term Position -> Qualifier -> Env ValueInfo

  op evaluateTranslate : SpecCalc.Term Position -> TranslateExpr Position
                        -> Env ValueInfo
}
\end{spec}
