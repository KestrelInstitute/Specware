\subsection{Evalution of a PSL Spec}

The prefix "P" is problematic here. In other place it refers
to PSort etc for "position" and other people think of
the P as parameterized spec.

\begin{spec}
SpecCalc qualifying spec {
  import New
  import ../PSpec
  import ../Utilities
  import /Languages/SpecCalculus/Semantics/Evaluate/Signature
  import /Library/Legacy/DataStructures/ListUtilities
\end{spec}

\begin{spec}
  sort SpecCalc.OtherValue = PSpec
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

So we have a problem. This does not fit withing the paradigm
so far. Does the global context map names to things representing procedures,
or names to spec like things that include procedures. I think the latter.
They are procedures in context.

\begin{spec}
  op SpecCalc.evaluatePSpec : List (PSpecElem Position) -> SpecCalc.Env ValueInfo
  def SpecCalc.evaluatePSpec pSpecElements = {
     base <- basePSpec;
     (pSpec,timeStamp,depURIs) <- evaluatePSpecElems base pSpecElements;
     dyCtxt <- dynamicSpec pSpec;
     statCtxt <- staticSpec pSpec;
     statCtxtElab <- elaborateSpec statCtxt; 
     dyCtxtElab <- elaborateInContext dyCtxt statCtxt; 
     newPSpec <- setDynamicSpec pSpec dyCtxtElab;
     newPSpec <- setStaticSpec newPSpec statCtxtElab;
     return (Other newPSpec,timeStamp,depURIs)
   }
\end{spec}

\begin{spec}
  op evaluatePSpecElems :
           PSpec
        -> List (PSpecElem Position)
        -> SpecCalc.Env (PSpec * TimeStamp * URI_Dependency)

  def SpecCalc.evaluatePSpecElems initialPSpec pSpecElems = {
      (pSpecWithImports,timeStamp,depURIs)
          <- foldM evaluatePSpecImportElem (initialPSpec,0,[]) pSpecElems;
      pSpec <- foldM evaluatePSpecContextElem pSpecWithImports pSpecElems;
      pSpec <- foldM evaluatePSpecProcElem pSpec pSpecElems;
      return (pSpec,timeStamp,depURIs)
    }
  
  op evaluatePSpecImportElem :
           (PSpec * TimeStamp * URI_Dependency)
        -> PSpecElem Position
        -> SpecCalc.Env (PSpec * TimeStamp * URI_Dependency)
  def evaluatePSpecImportElem (val as (pSpec,currentTimeStamp,currentDeps)) (elem,position) =
    case elem of
      | Import term -> {
            (value,importTimeStamp,depURIs) <- evaluateTermInfo term;
            (case value of
              | Other impPSpec -> {
                    newStatic <- mergeImport term impPSpec.staticSpec pSpec.staticSpec position;
                    newDynamic <- mergeImport term impPSpec.dynamicSpec pSpec.dynamicSpec position;
                    newPSpec <- setStaticSpec pSpec newStatic;
                    newPSpec <- setDynamicSpec newPSpec newDynamic;
                    newPSpec <- setProcedures newPSpec (foldMap
                            (fn newMap -> fn d -> fn c -> PolyMap.update newMap d c)
                                  newPSpec.procedures impPSpec.procedures);
                    return (newPSpec, max (currentTimeStamp,importTimeStamp), listUnion (currentDeps, depURIs))
                  }
              | Spec impSpec -> {
                    newStatic <- mergeImport term impSpec pSpec.staticSpec position;
                    newPSpec <- setStaticSpec pSpec newStatic;
                    return (newPSpec, max (currentTimeStamp,importTimeStamp), listUnion (currentDeps, depURIs))
                  }
              | _ -> raise (Fail ("Import not a spec")))
          }
      | _ -> return val

  op evaluatePSpecProcElem :
           PSpec
        -> PSpecElem Position
        -> SpecCalc.Env PSpec

  op evaluatePSpecContextElem :
           PSpec
        -> PSpecElem Position
        -> SpecCalc.Env PSpec
  def evaluatePSpecContextElem pSpec (elem, position) =
    case elem of
      | Sort (names,(tyVars,optSort)) -> {
            static <- staticSpec pSpec;
            static <- addSort names tyVars optSort static position;
            setStaticSpec pSpec static
          }
      | Def ([qid as Qualified(qual,id)],(fxty,srtScheme,optTerm)) -> {
            static <- staticSpec pSpec;
            case findAQualifierMap (static.ops, qual, id) of
              | None -> {
                  dynamic <- dynamicSpec pSpec;
                  (case findAQualifierMap (dynamic.ops, qual, id) of
                     | None -> raise (SpecError (position,
                                "Identifier "
                               ^ (printQualifiedId qid)
                               ^ " has not be declared as an operator nor as a variable"))
                     | Some _ -> {
                          dynamic <- addOp [qid] fxty srtScheme optTerm dynamic position;
                          setDynamicSpec pSpec dynamic
                        })
                 }
              | Some _ -> {
                   static <- addOp [qid] fxty srtScheme optTerm static position;
                   setStaticSpec pSpec static
                 }
          }
      | Var (names,(fxty,srtScheme,optTerm)) -> {
            dynamic <- dynamicSpec pSpec;
            dynamic <- addOp names fxty srtScheme optTerm dynamic position;
            setDynamicSpec pSpec dynamic
          }
      | Op (names,(fxty,srtScheme,optTerm)) -> {
            static <- staticSpec pSpec;
            static <- addOp names fxty srtScheme optTerm static position;
            setStaticSpec pSpec static
          }
      | Claim (Invariant, name, tyVars, term) -> {
            dynamic <- dynamicSpec pSpec;
            dynamic <- return (addAxiom ((name,tyVars,term), dynamic));
            setDynamicSpec pSpec dynamic
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
           PSpec
        -> PSpecElem Position
        -> SpecCalc.Env PSpec
  def evaluatePSpecDynamicContextElem pSpec (elem, position) =
    case elem of
      | _ -> return pSpec
\end{spec}

So how do we reconcile these things?  We construct a Spec with position,
and then we start construction the diagram for the body of some
procedure. Don't we want to elaborate as we go along?

\begin{spec}
  op PosSpec.mkTyVar : String -> ASort Position
  def PosSpec.mkTyVar name = TyVar (name, internalPosition)

  op staticBase : SpecCalc.Env Spec
  def staticBase = {
      baseURI <- pathToRelativeURI "/Library/PSL/Base";
      (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "PSL base") baseURI;
      return baseSpec
    }

  op baseSpec : SpecCalc.Env Spec
  def baseSpec = {
      baseURI <- pathToRelativeURI "/Library/Base";
      (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "Specware base") baseURI;
      return baseSpec
    }

  op basePSpec : SpecCalc.Env PSpec
  def basePSpec = {
    base <- staticBase;
    dynamicSpec <- return emptySpec;
    return {
        staticSpec = base,
        dynamicSpec = dynamicSpec,
        procedures = PolyMap.emptyMap
      }
  }
}
\end{spec}
