\section{Evalution of a term in the Spec Calculus}

Derived from r1.5 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSig.sl

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

  op evaluateDiag  : List (DiagElem Position) -> Env ValueInfo

  op evaluateDiagMorph :
      (SpecCalc.Term Position)
    * (SpecCalc.Term Position)
    * (List (DiagMorphElem Position))
    -> Env ValueInfo

  op evaluateLispCompile: ValueInfo * SpecCalc.Term Position * Option String
			  -> Env ValueInfo

  op evaluateTerm : SpecCalc.Term  Position -> Env Value

  op evaluateTermInfo : SpecCalc.Term  Position -> Env ValueInfo

  op evaluateLet : List (Decl Position) -> SpecCalc.Term Position
                  -> Env ValueInfo
  op qualifySpec : Spec -> Qualifier -> Env Spec

  op evaluateTranslate : SpecCalc.Term Position -> TranslateExpr Position
                        -> Env ValueInfo
}
\end{spec}
