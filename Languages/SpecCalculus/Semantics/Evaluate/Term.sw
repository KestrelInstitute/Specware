\subsection{Interpreter for Spec Calculus}

Synchronized with r1.9 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalTerm.sl

\begin{spec}
SpecCalc qualifying spec {
 % import Signature          
 import URI          
 import Spec         
 import Let         
 import Qualify         
 import Diagram      
 import Colimit
 import SpecMorphism 
 import DiagMorphism 
 import Generate      
 import Snark
 import Translate      
 import Obligations
 import Substitute      
 import Print      
 import /Languages/MetaSlang/CodeGen/C/ToC
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

    | URI uri -> SpecCalc.evaluateURI (positionOf term) uri

    | Spec elems -> SpecCalc.evaluateSpec elems

    | SpecMorph fields -> SpecCalc.evaluateSpecMorph fields

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

    | Generate (language, sub_term as (term,position), optFile) -> {
          (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo sub_term;
          baseURI <- pathToRelativeURI "/Library/Base";
          (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base") baseURI;
          (case value of
            | Spec spc -> 
                (case language of
                   | "lisp" -> evaluateLispCompile ((value,timeStamp,depURIs),
						   sub_term,optFile)
                   | "snark" -> evaluateSnarkGen ((value,timeStamp,depURIs),
						   sub_term,optFile)
                   | "spec" -> {
                          print (showValue value);
                          return (value,timeStamp,depURIs)
                        }
                   | "c" -> 
                         let _ = specToC (subtractSpec spc baseSpec) in
                         return (value,timeStamp,depURIs)
                   | lang -> raise (Unsupported ((positionOf sub_term),
                                  "no generation for language "
                                ^ lang
                                ^ " yet")))
            | _ -> raise (TypeCheck ((positionOf sub_term),
                        "attempting to generate code from an object that is not a specification")))
        }
}
\end{spec}
