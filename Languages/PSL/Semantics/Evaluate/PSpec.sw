\subsection{Evalution of a PSL Spec}

The prefix "P" is problematic here. In other place it refers
to PSort etc for "position" and other people think of
the P as parameterized spec.

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/PosSpec
  import Spec
  import Spec/Utilities
  import URI/Utilities
  import ../Utilities
  import New
  import Util
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
%   op evaluatePSpecElems :
%            PSpec Position
%         -> List (PSpecElem Position)
%         -> Env (PSpec Position * TimeStamp * URI_Dependency)

  def evaluatePSpecElems initialPSpec pSpecElems = {
      (pSpecWithImports,timeStamp,depURIs)
          <- foldM evaluatePSpecImportElem (initialPSpec,0,[]) pSpecElems;
      pSpec <- foldM evaluatePSpecStaticContextElem pSpecWithImports pSpecElems;
      static <- staticSpec pSpec;
      dynamic <- dynamicSpec pSpec;
      staticElab <- elaborateSpec static;
      uri <- pathToRelativeURI "Static";
      dynamic <- mergeImport (URI uri,internalPosition) staticElab dynamic internalPosition;
      pSpec <- setDynamicSpec pSpec dynamic;
      pSpec <- foldM evaluatePSpecDynamicContextElem pSpec pSpecElems;
      dynamicElab <- elaborateSpec dynamic; 
      pSpec <- foldM evaluatePSpecProcElem pSpec pSpecElems;
      return (pSpec,timeStamp,depURIs)
    }

  op evaluatePSpecImportElem :
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

  op evaluatePSpecProcElem :
           PSpec Position
        -> PSpecElem Position
        -> Env (PSpec Position)

  op evaluatePSpecStaticContextElem :
           PSpec Position
        -> PSpecElem Position
        -> Env (PSpec Position)
  def evaluatePSpecStaticContextElem pSpec (elem, position) =
    case elem of
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
            static <- staticSpec pSpec;
            static <- return (addAxiom ((name,tyVars,term), static));
            setStaticSpec pSpec static
          }
      | Claim (Theorem, name, tyVars, term) -> {
            static <- staticSpec pSpec;
            static <- return (addTheorem ((name,tyVars,term), static));
            setStaticSpec pSpec static
          }
      | Claim (Conjecture, name, tyVars, term) -> {
            static <- staticSpec pSpec;
            static <- return (addConjecture ((name,tyVars,term), static));
            setStaticSpec pSpec static
          }
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"
      | _ -> return pSpec

  op evaluatePSpecDynamicContextElem :
           PSpec Position
        -> PSpecElem Position
        -> Env (PSpec Position)
  def evaluatePSpecDynamicContextElem pSpec (elem, position) =
    case elem of
      | Var (names,(fxty,srtScheme,optTerm)) -> {
            dynamic <- dynamicSpec pSpec;
            dynamic <- addOp names fxty srtScheme optTerm dynamic position;
            setStaticSpec pSpec dynamic
          }
      | _ -> return pSpec
\end{spec}

So how do we reconcile these things?
We construct a Spec with position, and then we start construction the diagram for the
body of some procedure. Don't we want to elaborate as we go along?

\begin{spec}
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
                      PosSpec.mkPBase (unQualified "Delta", [PosSpec.mkTyVar "store"])],
                    PosSpec.boolPSort)));
    staticSpec <- addSort [unQualified "Delta"] ["a"] deltaSort emptySpec internalPosition;
    staticSpec <- addSort [unQualified "Proc"]  ["args","rtn","store"] procSort staticSpec internalPosition;
    dynamicSpec <- return emptySpec;
    % let dynamic = addImport ("Static", dynamic)
    return {
        staticSpec = staticSpec,
        dynamicSpec = dynamicSpec,
        procedures = PolyMap.emptyMap
      }
  }
}
\end{spec}
