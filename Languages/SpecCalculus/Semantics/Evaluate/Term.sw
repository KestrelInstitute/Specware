\subsection{Interpreter for Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
 % import Signature          
 import UnitId          
 import Spec         
 import Let         
 import Qualify         
 import Diagram      
 import Colimit
 import SpecMorphism 
 import ExtendMorphism 
 import DiagMorphism 
 import Generate      
 import Translate      
 import Obligations
 import Substitute      
 import Print      
 import Prove
 import Reduce
\end{spec}

This is a monadic interpreter for the Spec Calculus.

\begin{spec}
 def SpecCalc.evaluateTerm term =
   {(value,_,_) <- SpecCalc.evaluateTermInfo term;
    return value}

 def SpecCalc.evaluateTermInfo term =
   let pos = positionOf term in
   case (valueOf term) of
    | Print term -> SpecCalc.evaluatePrint term

    | UnitId unitId -> SpecCalc.evaluateUID (positionOf term) unitId

    | Spec elems -> SpecCalc.evaluateSpec elems pos

    | SpecMorph fields -> SpecCalc.evaluateSpecMorph fields

    | ExtendMorph term -> SpecCalc.evaluateExtendMorph term

    | Diag elems -> SpecCalc.evaluateDiag elems

    | Colimit sub_term -> SpecCalc.evaluateColimit sub_term

    | Subst args   -> SpecCalc.evaluateSubstitute  args pos

    | DiagMorph fields -> SpecCalc.evaluateDiagMorph fields

    | Qualify (sub_term, qualifier) -> SpecCalc.evaluateQualify sub_term qualifier

    | Let (decls, sub_term) -> SpecCalc.evaluateLet decls sub_term

    | Where (decls, sub_term) -> SpecCalc.evaluateLet decls sub_term

    | Hide (names, sub_term) -> {
          print "hide request ignored\n";
          SpecCalc.evaluateTermInfo sub_term
        }

    | Export (names, sub_term) -> {
          print "export request ignored\n";
          SpecCalc.evaluateTermInfo sub_term
        }

    | Translate (sub_term, translation) ->
        SpecCalc.evaluateTranslate sub_term translation

    | Obligations(sub_term) -> SpecCalc.evaluateObligations sub_term

    | Prove args -> SpecCalc.evaluateProve args pos

    | Generate args -> SpecCalc.evaluateGenerate args pos

    | Reduce (msTerm,scTerm) -> SpecCalc.reduce msTerm scTerm pos

    | Other args -> SpecCalc.evaluateOther args pos  % used for extensions to Specware
}
\end{spec}
