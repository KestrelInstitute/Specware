\subsection{Interpreter for Spec Calculus}

Synchronized with r1.9 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalTerm.sl

\begin{spec}
SpecCalc qualifying spec {
 % import Signature          
 import URI          
 import Spec         
 import Let         
 import Qualify         
 import SpecMorphism 
 import Diagram      
 import Generate      
 import Translate      
\end{spec}

This is a monadic interpreter for the Spec Calculus.

\begin{spec}
 def SpecCalc.evaluateTerm term =
   {(value,_,_) <- SpecCalc.evaluateTermInfo term;
    return value}

 def SpecCalc.evaluateTermInfo term =
   case (valueOf term) of
    | Print term -> {
          (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
          print (showValue value);
          return (value,timeStamp,depURIs)
        }

    | URI uri -> SpecCalc.evaluateURI (positionOf term) uri

    | Spec elems -> SpecCalc.evaluateSpec elems

    | SpecMorph fields -> SpecCalc.evaluateSpecMorph fields

    | Diag elems -> SpecCalc.evaluateDiag elems

    | DiagMorph fields -> SpecCalc.evaluateDiagMorph fields

    | Qualify (sub_term, qualifier) -> {
          (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo sub_term;
          case value of
            | Spec spc -> {
                  qualified_spec <- qualifySpec spc qualifier;
                          return (Spec qualified_spec,timeStamp,depURIs)
                }
            | _ -> raise (TypeCheck ((positionOf term),
                            "qualifying a term that is not a specification"))
        }

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

    | Generate (language, sub_term as (term,position), optFile) -> {
          (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo sub_term;
          (case value of
            | Spec spc -> 
                (case language of
                   | "lisp" -> evaluateLispCompile ((value,timeStamp,depURIs),
						   sub_term,optFile)
                   | "spec" -> {
                          print (showValue value);
                          return (value,timeStamp,depURIs)
                        }
                   | lang -> raise (Unsupported ((positionOf sub_term),
                                  "no generation for language "
                                ^ lang
                                ^ "yet")))
            | _ -> raise (TypeCheck ((positionOf sub_term),
                        "compiling a term that is not a specification")))
        }
}
\end{spec}
