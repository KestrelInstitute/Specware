\subsection{Evalution of a Spec form in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec
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
    (pos_spec,TS,depUIDs) <-
      evaluateSpecElems
	(markUnQualified % even the empty spec!
	 (if anyImports? spec_elements
	    then emptySpec % some import will include baseSpec
	  else importOfSpec(optBaseUnitId,baseSpec)))
	spec_elements;
    elaborated_spec <- elaborateSpecM pos_spec;
    compressed_spec <- complainIfAmbiguous (compressDefs elaborated_spec) position;
%    full_spec <- explicateHiddenAxiomsM compressed_spec;
    return (Spec (removeDuplicateImports compressed_spec),TS,depUIDs)
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
      (TS,depUIDs) <- foldM checkImports (0,[]) specElems;
      fullSpec <- foldM evaluateSpecElem starting_spec specElems;
      return (fullSpec,TS,depUIDs)
    }

  op  checkImports : (TimeStamp * UnitId_Dependency)
                     -> SpecElem Position
                     -> SpecCalc.Env (TimeStamp * UnitId_Dependency)
  def checkImports val (elem, position) =
    case elem of
      | Import terms -> 
        foldM (fn (cTS,cDepUIDs) -> fn term ->
	       {
		(value,iTS,depUIDs) <- evaluateTermInfo term;
		(case coerceToSpec value of
		   | Spec _ -> return (max(cTS,iTS), listUnion(cDepUIDs,depUIDs))
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
      | Import terms ->
        foldM (fn spc -> fn term ->
	       {
		(value,_,_) <- evaluateTermInfo term;
		(case coerceToSpec value of
		   | Spec impSpec -> mergeImport term impSpec spc 
		   %% Already checked
		   | _ -> raise (Fail ("Shouldn't happen!")))
		  })
              spc               
              terms
      | Sort    (names,       dfn)               -> addSort names      dfn spc position
      | Op      (names, fxty, dfn)               -> addOp   names fxty dfn spc position

      | Claim   (Axiom,      name, tyVars, term) -> return (addAxiom      ((name,tyVars,term), spc)) 
      | Claim   (Theorem,    name, tyVars, term) -> return (addTheorem    ((name,tyVars,term), spc))
      | Claim   (Conjecture, name, tyVars, term) -> return (addConjecture ((name,tyVars,term), spc))
      | Claim   _                                -> error "evaluateSpecElem: unsupported claim type"

      | Pragma  (prefix, body, postfix)          -> return (addPragma     ((prefix, body, postfix, position), spc))
      | Comment str                              -> return (addComment    (str,                     spc))

  def mergeImport spec_term imported_spec old_spec =
    let sorts = old_spec.sorts in
    let ops   = old_spec.ops   in
    {
     new_spec  <- return (addImport ((spec_term, imported_spec), old_spec));

     new_sorts <- if sorts = emptySpec.sorts then 
                    return imported_spec.sorts
		  else 
		    %% TODO: fold over just infos?
		    foldOverQualifierMap (fn (_, _, info, sorts) ->
					  return (mergeSortInfo sorts info))
		                         sorts 
				         imported_spec.sorts;

     new_ops   <- if ops = emptySpec.ops then 
                    return imported_spec.ops
		  else 
		    %% TODO: fold over just infos?
		    foldOverQualifierMap (fn (_, _, info, ops) ->
					  return (mergeOpInfo ops info))
		                         ops
					 imported_spec.ops;

    return (new_spec << {sorts = new_sorts,
			 ops   = new_ops})
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
endspec
\end{spec}
