\subsection{Evalution of a PSL Spec}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/PosSpec
  import Spec/Utilities
  import ../Utilities
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

So we have a problem. This does not fit withing the paradigm
so far. Does the global context map names to things representing procedures,
or names to spec like things that include procedures. I think the latter.
They are procedures in context.

\begin{spec}
 op SpecCalc.evaluatePSpec :
   List (PSpecElem Position)
       -> SpecCalc.Env ValueInfo
 def SpecCalc.evaluatePSpec pSpecElements = {
    base <- basePSpec;
    (pSpec,timeStamp,depURIs) <- evaluatePSpecElems base pSpecElements;
    return (PSpec pSpec,timeStamp,depURIs)
  }
\end{spec}
\begin{spec}
  op evaluatePSpecElems :
           PSpec Position
        -> List (PSpecElem Position)
        -> Env (PSpec Position * TimeStamp * URI_Dependency)

  def evaluatePSpecElems initialPSpec pSpecElems = {
      (pSpecWithImports,timeStamp,depURIs)
          <- foldM evaluatePSpecImport (initialPSpec,0,[]) pSpecElems;
      fullPSpec <- foldM evaluatePSpecElem pSpecWithImports pSpecElems;
      return (fullPSpec,timeStamp,depURIs)
    }

  op evaluatePSpecImport :
           (PSpec Position * TimeStamp * URI_Dependency)
        -> PSpecElem Position
        -> Env (PSpec Position * TimeStamp * URI_Dependency)
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
           PSpec Position
        -> PSpecElem Position
        -> Env (PSpec Position)
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
\end{spec}

So how do we reconcile these things?
We construct a Spec with position, and then we start construction the diagram for the
body of some procedure. Don't we want to elaborate as we go along?

\begin{spec}
  op unQual : String -> QualifiedId
  def unQual id = Qualified (UnQualified, id)

  op PosSpec.mkTyVar : String -> ASort Position
  def PosSpec.mkTyVar name = TyVar (name, internalPosition)

  op basePSpec : SpecCalc.Env (PSpec Position)
  def basePSpec = {
    deltaSort <- return (Some (PosSpec.mkProduct [PosSpec.mkTyVar "a", PosSpec.mkTyVar "a"]));
    procSort <- return (Some
                 (PosSpec.mkArrow
                   (PosSpec.mkProduct [
                      PosSpec.mkTyVar "args",
                      PosSpec.mkTyVar "rtn",
                      PosSpec.mkPBase (unQual "Delta", [PosSpec.mkTyVar "store"])],
                    PosSpec.boolPSort)));
    staticSpec <- addSort [unQual "Delta"] ["a"] deltaSort emptySpec internalPosition;
    staticSpec <- addSort [unQual "Proc"]  ["args","rtn","store"] procSort staticSpec internalPosition;
    staticSpec <- elaborateSpec staticSpec;
    dynamicSpec <- return emptySpec;
    % let dynamic = addImport ("Static", dynamic)
    axiomSpec <- return emptySpec;
    % let axiomSpec = addImport ("Static", axmSpec)
    return {
        staticSpec = staticSpec,
        dynamicSpec = dynamicSpec,
        axiomSpec = axiomSpec,
        procedures = PolyMap.emptyMap
      }
  }

 op elaborateSpec : PosSpec -> Env Spec
 def elaborateSpec spc =
   case elaboratePosSpec (spc, "internal") of
       | Ok pos_spec -> return pos_spec % (convertPosSpecToSpec pos_spec)
       | Error msg   -> raise  (OldTypeCheck msg)
}
\end{spec}
