\subsection{Evalution of a Spec form in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import UnitId/Utilities
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Transformations/DefToAxiom
  import Spec/MergeSpecs
  import Spec/CompressSpec
  import Spec/AddSpecElements
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

\begin{spec}
 op  noElaboratingMessageFiles: List String
 def noElaboratingMessageFiles = []

 def SpecCalc.evaluateSpec spec_elements position = {
    unitId <- getCurrentUID;
    unitStr <- return (uidToString unitId);
    when (~(member(unitStr,noElaboratingMessageFiles)))
       (print (";;; Elaborating spec at " ^ unitStr ^ "\n"));
    (optBaseUnitId,baseSpec) <- getBase;
    (pos_spec,TS,depUIDs) <- evaluateSpecElems (if anyImports? spec_elements
						  then emptySpec % some import will include baseSpec
						  else baseSpec)
		               spec_elements;
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
  def evaluateSpecElems starting_spec specElems = {
      %% Use the name starting_spec to avoid any possible confusion with the
      %% op initialSpecInCat, which refers to the initial spec in the category of specs.
      (spcWithImports,TS,depUIDs) <- foldM evaluateSpecImport (starting_spec,0,[]) specElems;
      fullSpec <- foldM evaluateSpecElem spcWithImports specElems;
      return (fullSpec,TS,depUIDs)
    }

  op evaluateSpecImport : (ASpec Position * TimeStamp * UnitId_Dependency)
                          -> SpecElem Position
                          -> SpecCalc.Env (ASpec Position * TimeStamp * UnitId_Dependency)
  def evaluateSpecImport val (elem, position) =
    case elem of
      | Import terms -> 
        foldM (fn (spc,cTS,cDepUIDs) -> fn term ->
	       {
		(value,iTS,depUIDs) <- evaluateTermInfo term;
		(case coerceToSpec value of
		   | Spec impSpec -> {
				      newSpc <- mergeImport term impSpec spc position;
				      return (newSpc, max(cTS,iTS), listUnion(cDepUIDs,depUIDs))
				     }
		   | InProcess -> 
		     (case (valueOf term) of
			| UnitId (UnitId_Relative   x) -> raise (CircularDefinition x)
			| UnitId (SpecPath_Relative x) -> raise (CircularDefinition x)
			| _ -> raise (Fail ("Circular import")))

		   | _ -> raise (Fail ("Import not a spec")))
		  })
              val               
              (rev terms) % just so result shows in same order as read
      | _ -> return val

  op  anyImports?: List (SpecElem Position) -> Boolean
  def anyImports? specElems =
    exists (fn (elem,_) -> case elem of Import _ -> true | _ -> false) specElems

  op evaluateSpecElem : ASpec Position
                          -> SpecElem Position
                          -> SpecCalc.Env (ASpec Position)
  def evaluateSpecElem spc (elem, position) =
    case elem of
      | Import terms -> return spc
      | Sort (names, dfn) ->
          addSort names dfn spc position
      | Op (names, fxty, dfn) ->
          addOp names fxty dfn spc position
      | Claim (Axiom, name, tyVars, term) ->
          return (addAxiom ((name,tyVars,term), spc)) 
      | Claim (Theorem, name, tyVars, term) ->
          return (addTheorem ((name,tyVars,term), spc))
      | Claim (Conjecture, name, tyVars, term) ->
          return (addConjecture ((name,tyVars,term), spc))
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"

  def mergeImport spec_term imported_spec spec_a position =
    let def mergeSortStep (imported_qualifier, imported_id, imported_sort_info, (spc, combined_sorts)) =
      let oldSortInfo = findAQualifierMap (combined_sorts,imported_qualifier, imported_id) in {
          mergedSorts <- SpecCalc.mergeSortInfo imported_sort_info oldSortInfo position;
          return (spc,
		  insertAQualifierMap (combined_sorts,
                                       imported_qualifier,
                                       imported_id,
                                       mergedSorts))
        } in
    let def mergeOpStep (imported_qualifier, imported_id, imported_op_info, (spc, combined_ops)) =
      let oldOpInfo = findAQualifierMap (combined_ops,imported_qualifier, imported_id) in {
           mergedOps <- SpecCalc.mergeOpInfo imported_op_info oldOpInfo position;
           return (spc,
		   insertAQualifierMap (combined_ops,
                                        imported_qualifier,
                                        imported_id,
                                        mergedOps))
        } in
    {
      spec_b <- return (addImport ((spec_term, imported_spec), spec_a)); 
      (_, sorts_b) <- if spec_a = emptySpec then return (spec_b,imported_spec.sorts)
                       else foldOverQualifierMap mergeSortStep (spec_b, spec_b.sorts) imported_spec.sorts;
      spec_c <- return (setSorts (spec_b, sorts_b));
      (_, ops_c) <- if spec_a = emptySpec then return (spec_c,imported_spec.ops)
                     else foldOverQualifierMap mergeOpStep (spec_c, spec_c.ops) imported_spec.ops;
      spec_d <- return (setOps (spec_c, ops_c));
      spec_e <- return (setProperties (spec_d, if spec_a = emptySpec then imported_spec.properties
					        else listUnion (imported_spec.properties,spec_d.properties)));
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
