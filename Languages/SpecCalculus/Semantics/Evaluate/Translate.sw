\subsection{Evalution of Spec Translations}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
\end{spec}

Perhaps evaluating a translation should yield a morphism rather than just 
a spec. Then perhaps we add dom and cod domain operations on morphisms.
Perhaps the calculus is getting too complicated.

\begin{spec}
  def SpecCalc.evaluateTranslate term translation = {
      (value,timeStamp,depURIs) <- evaluateTermInfo term;
      case value of
        | Spec spc -> {
              spcTrans <- translateSpec spc translation;
              return (Spec spcTrans,timeStamp,depURIs)
            }
        | _ -> raise (TypeCheck (positionOf term,
                         "translating a term that is not a specification"))
    }
\end{spec}

To translate a spec means to recursively descend the hierarchy of imports
and translate names. This can raise exceptions since ops may end up with
the same names.

\begin{spec}
  op translateSpec : Spec -> TranslateExpr Position -> Env Spec
  def translateSpec spc expr = {
      print ("ignoring:  translation \n");
      return spc
    }
}
\end{spec}
