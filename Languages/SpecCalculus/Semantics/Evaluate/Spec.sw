\subsection{Evalution of a Spec term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import UnitId/Utilities
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Transformations/DefToAxiom
  import Spec/Utilities
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

\begin{spec}
 def SpecCalc.evaluateSpec spec_elements position = {
    unitId <- getCurrentUID;
    print (";;; Processing spec at " ^ (uidToString unitId) ^ "\n");
    (optBaseUnitId,baseSpec) <- getBase;
    (pos_spec,TS,depUIDs) <- evaluateSpecElems baseSpec spec_elements;
    elaborated_spec <- elaborateSpecM pos_spec;
    compressed_spec <- complainIfAmbiguous (compressDefs elaborated_spec) position;
%    full_spec <- explicateHiddenAxiomsM compressed_spec;
    return (Spec compressed_spec,TS,depUIDs)
  }
\end{spec}

We first evaluate the imports and then the locally declared ops, sorts
axioms, etc.

\begin{spec}
  op evaluateSpecElems : ASpec Position -> List (SpecElem Position)
                           -> SpecCalc.Env (ASpec Position * TimeStamp * UnitId_Dependency)
  def evaluateSpecElems initialSpec specElems = {
      (spcWithImports,TS,depUIDs) <- foldM evaluateSpecImport (initialSpec,0,[]) specElems;
      fullSpec <- foldM evaluateSpecElem spcWithImports specElems;
      return (fullSpec,TS,depUIDs)
    }

  op evaluateSpecImport : (ASpec Position * TimeStamp * UnitId_Dependency)
                          -> SpecElem Position
                          -> SpecCalc.Env (ASpec Position * TimeStamp * UnitId_Dependency)
  def evaluateSpecImport (val as (spc,cTS,cDepUIDs)) (elem, position) =
    case elem of
      | Import term -> {
            (value,iTS,depUIDs) <- evaluateTermInfo term;
            (case coerceToSpec value of
              | Spec impSpec -> {
                    newSpc <- mergeImport term impSpec spc position;
                    return (newSpc, max(cTS,iTS), listUnion(cDepUIDs,depUIDs))
                  }
              | _ -> raise (Fail ("Import not a spec")))
          }
      | _ -> return val

  op evaluateSpecElem : ASpec Position
                          -> SpecElem Position
                          -> SpecCalc.Env (ASpec Position)
  def evaluateSpecElem spc (elem, position) =
    case elem of
      | Import term -> return spc
      | Sort (names,(tyVars,defs)) ->
          addSort names tyVars defs spc position
      | Op (names,(fxty,srtScheme,defs)) ->
          addOp names fxty srtScheme defs spc position
      | Claim (Axiom, name, tyVars, term) ->
          return (addAxiom ((name,tyVars,term), spc)) 
      | Claim (Theorem, name, tyVars, term) ->
          return (addTheorem ((name,tyVars,term), spc))
      | Claim (Conjecture, name, tyVars, term) ->
          return (addConjecture ((name,tyVars,term), spc))
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"

  def mergeImport spec_term imported_spec spec_a position =
    let def mergeSortStep (imported_qualifier, imported_id, imported_sort_info, combined_sorts) =
      let oldSortInfo = findAQualifierMap (combined_sorts,imported_qualifier, imported_id) in {
          mergedSorts <- SpecCalc.mergeSortInfo imported_sort_info oldSortInfo position;
          return (insertAQualifierMap (combined_sorts,
                                       imported_qualifier,
                                       imported_id,
                                       mergedSorts))
        } in
    let def mergeOpStep (imported_qualifier, imported_id, imported_op_info, combined_ops) =
      let oldOpInfo = findAQualifierMap (combined_ops,imported_qualifier, imported_id) in {
           mergedOps <- SpecCalc.mergeOpInfo imported_op_info oldOpInfo position;
           return (insertAQualifierMap (combined_ops,
                                        imported_qualifier,
                                        imported_id,
                                        mergedOps))
        } in
    {
      spec_b <- return (addImport ((spec_term, imported_spec), spec_a)); 
      sorts_b <- foldOverQualifierMap mergeSortStep spec_b.sorts imported_spec.sorts;
      spec_c <- return (setSorts (spec_b, sorts_b));
      ops_c <- foldOverQualifierMap mergeOpStep spec_c.ops imported_spec.ops;
      spec_d <- return (setOps (spec_c, ops_c));
      spec_e <- return (setProperties (spec_d, listUnion (spec_d.properties,imported_spec.properties)));
      return spec_e
    }
\end{spec}

The following wraps the existing \verb+elaborateSpec+ in a monad until
such time as the current one can made monadic.

\begin{spec}
 op elaborateSpecM : Spec -> SpecCalc.Env Spec
 def elaborateSpecM spc =
   { unitId      <- getCurrentUID;
     filename <- return ((uidToFullPath unitId) ^ ".sw");
     case elaboratePosSpec (spc, filename) of
       | Spec spc    -> return spc
       | Errors msgs -> raise (TypeCheckErrors msgs)
   }
\end{spec}

\begin{spec}
  op explicateHiddenAxiomsM: Spec -> SpecCalc.Env Spec
  def explicateHiddenAxiomsM spc =
    return spc % (explicateHiddenAxioms spc)
}
\end{spec}
