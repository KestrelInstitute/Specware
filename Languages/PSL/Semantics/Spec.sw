\subsection{Evalution of a PSL Spec}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  % import /Languages/SpecCalculus/Semantics/Evaluate/URI/Utilities
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  % import /Languages/SpecCalculus/Semantics/Evaluate/Spec/Utilities
  import Utilities
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

So we have a problem. This does not fit withing the paradigm
so far. Does the global context map names to things representing procedures,
or names to spec like things that include procedures. I think the latter.
They are procedures in context.

\begin{spec}
 op basePSpec : fa (a) PSpec a

 op SpecCalc.evaluatePSpec :
   fa (a) List (PSpecElem a)
       -> SpecCalc.Env ValueInfo
 def SpecCalc.evaluatePSpec pSpecElements = {
    (pSpec,timeStamp,depURIs) <- evaluatePSpecElems basePSpec pSpecElements;
    return (PSL pSpec,timeStamp,depURIs)
  }
\end{spec}
\begin{spec}
  op evaluatePSpecElems :
    fa (a) PSpec a
        -> List (PSpecElem a)
        -> Env (PSpec Position * TimeStamp * URI_Dependency)

  def evaluatePSpecElems initialPSpec pSpecElems = {
      (pSpecWithImports,timeStamp,depURIs)
          <- foldM evaluatePSpecImport (initialPSpec,0,[]) pSpecElems;
      fullPSpec <- foldM evaluatePSpecElem pSpecWithImports pSpecElems;
      return (fullPSpec,timeStamp,depURIs)
    }

  op evaluatePSpecImport :
    fa (a) (PSpec a * TimeStamp * URI_Dependency)
        -> PSpecElem a
        -> Env (ASpec Position * TimeStamp * URI_Dependency)
%   def evaluatePSpecImport (val as (pSpec,currentTimeStamp,currentDeps)) (elem,position) =
%     case elem of
%       | Import term -> {
%             (value,importTimeStamp,depURIs) <- evaluateTermInfo term;
%             (case value of
%               | PSL impPSpec -> return (value,importTimeStamp,depURIs)
%               | Spec impSpec -> {
%                     newSpc <- mergeImport term impSpec spc position;
%                     return (newSpc, max (currentTimeStamp,importTimeStamp), currentDeps ++ depURIs)
%                   }
%               | _ -> raise (Fail ("Import not a spec")))
%           }
%       | _ -> return val

  op evaluatePSpecElem :
    fa (a) PSpec a
        -> PSpecElem a
        -> Env (PSpec a)
  def evaluatePSpecElem pSpec (elem, position) =
    case elem of
      | Import term -> return pSpec
      | Sort (names,(tyVars,optSort)) -> {
            static <- staticSpec pSpec;
            static <- addSort names tyVars optSort static position;
            setStaticSpec pSpec static
          }
      | Op (names,(fxty,srtScheme,optTerm)) -> {
            static <- staticSpec pSpec;
            x <- addOp names fxty srtScheme optTerm static position;
            setStaticSpec pSpec x
          }
      | Claim (Axiom, name, tyVars, term) -> {
            axioms <- axiomSpec pSpec;
            axioms <- return (addAxiom ((name,tyVars,term), axioms));
            setAxiomSpec pSpec axioms
          }
      | Claim (Theorem, name, tyVars, term) -> {
            axioms <- axiomSpec pSpec;
            axioms <- return (addTheorem ((name,tyVars,term), axioms));
            setAxiomSpec pSpec axioms
          }
      | Claim (Conjecture, name, tyVars, term) -> {
            axioms <- axiomSpec pSpec;
            axioms <- return (addConjecture ((name,tyVars,term), axioms));
            setAxiomSpec pSpec axioms
          }
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"

      | Var (names,(fxty,srtScheme,optTerm)) -> {
            dynamic <- dynamicSpec pSpec;
            dynamic <- addOp names fxty srtScheme optTerm dynamic position;
            setStaticSpec pSpec dynamic
          }
}
\end{spec}
