\subsection{Evalution of a PSL Spec}

The prefix "P" is problematic here. In other place it refers
to PSort etc for "position" and other people think of
the P as parameterized spec.

\begin{spec}
SpecCalc qualifying spec {
  % import /Languages/MetaSlang/Specs/PosSpec
  import Spec
  % import ../Utilities
  import New
  % import Signature 
  % import Util
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

So we have a problem. This does not fit withing the paradigm
so far. Does the global context map names to things representing procedures,
or names to spec like things that include procedures. I think the latter.
They are procedures in context.

\begin{spec}
 % op SpecCalc.evaluatePSpec :
 %         List (PSpecElem Position)
 %      -> SpecCalc.Env ValueInfo
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

  op fixPSpec : PSpec Position -> PSpec ()
  def fixPSpec pSpec = {
       staticSpec = convertPosSpecToSpec pSpec.staticSpec,
       dynamicSpec = convertPosSpecToSpec pSpec.dynamicSpec,
       procedures = pSpec.procedures
     } 

  def evaluatePSpecElems initialPSpec pSpecElems = {
      (pSpecWithImports,timeStamp,depURIs)
          <- foldM evaluatePSpecImportElem (initialPSpec,0,[]) pSpecElems;
      pSpec <- foldM evaluatePSpecStaticContextElem pSpecWithImports pSpecElems;
      % base <- baseSpec;
      % print "evaluatePSpecElems: .. after static and import\n";
      % print (ppFormat (ppPSpecLess (fixPSpec pSpec) base));
      % static <- staticSpec pSpec;
      % dynamic <- dynamicSpec pSpec;
      % staticElab <- elaborateSpec static;
      % uri <- pathToRelativeURI "Static";
      % dynamic <- mergeImport (URI uri,internalPosition) staticElab dynamic internalPosition;
      % pSpec <- setDynamicSpec pSpec dynamic;
      pSpec <- foldM evaluatePSpecDynamicContextElem pSpec pSpecElems;
      % print "evaluatePSpecElems: .. after dynamic before proc elements\n";
      % print (ppFormat (ppPSpecLess (fixPSpec pSpec) base));
      pSpec <- foldM evaluatePSpecProcElem pSpec pSpecElems;
      % print "evaluatePSpecElems: .. after proc elements\n";
      % print (ppFormat (ppPSpecLess (fixPSpec pSpec) base));
      return (pSpec,timeStamp,depURIs)
    }
  
  op baseSpec : SpecCalc.Env (ASpec ())
  def baseSpec = {
      (Spec base,_,_) <- SpecCalc.evaluateURI (Internal "base spec")
           (SpecPath_Relative {path = ["Library","Base"], hashSuffix = None});
      return base
    }

  op evaluatePSpecImportElem :
           (PSpec Position * TimeStamp * URI_Dependency)
        -> PSpecElem Position
        -> Env (PSpec Position * TimeStamp * URI_Dependency)
  def evaluatePSpecImportElem (val as (pSpec,currentTimeStamp,currentDeps)) (elem,position) =
    case elem of
      | Import term -> {
            (value,importTimeStamp,depURIs) <- evaluateTermInfo term;
            (case value of
              | PSpec impPSpec -> return (impPSpec,importTimeStamp,depURIs)  % This is wrong .. should merge!
              | Spec impSpec -> {
                    newStatic <- mergeImport term impSpec pSpec.staticSpec position;
                    newPSpec <- setStaticSpec pSpec newStatic;
                    return (newPSpec, max (currentTimeStamp,importTimeStamp), currentDeps ++ depURIs)
                  }
              | _ -> raise (Fail ("Import not a spec")))
          }
      | _ -> return val

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
            setDynamicSpec pSpec dynamic
          }
      | _ -> return pSpec
\end{spec}

So how do we reconcile these things?
We construct a Spec with position, and then we start construction the diagram for the
body of some procedure. Don't we want to elaborate as we go along?

\begin{spec}
  op PosSpec.mkTyVar : String -> ASort Position
  def PosSpec.mkTyVar name = TyVar (name, internalPosition)

  op staticBase : SpecCalc.Env (ASpec ())
  def staticBase = {
      (Spec base,_,_) <- SpecCalc.evaluateURI (Internal "static base spec")
           (SpecPath_Relative {path = ["Library","PSL","Base"], hashSuffix = None});
      return base
    }

  op basePSpec : SpecCalc.Env (PSpec Position)
  def basePSpec = {
    base <- staticBase;
    base <- return (convertSpecToPosSpec base);
    dynamicSpec <- return emptySpec;
    return {
        staticSpec = base,
        dynamicSpec = dynamicSpec,
        procedures = PolyMap.emptyMap
      }
  }
}
\end{spec}
