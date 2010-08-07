(* Evalution of a Spec form in the Spec Calculus *)

SpecCalc qualifying spec

  import /Library/Legacy/DataStructures/ListUtilities % for listUnion

  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/CompressSpec
  import /Languages/MetaSlang/Transformations/DefToAxiom

  import Signature 
  import UnitId/Utilities

  import Spec/AddSpecElements
  import Spec/MergeSpecs
  import Spec/ComplainIfAmbiguous
  import Transform

(*
To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.
*)

 op  noElaboratingMessageFiles: List String
 def noElaboratingMessageFiles = []

 def SpecCalc.evaluateSpec spec_elements position = {
    unitId <- getCurrentUID;
    unitStr <- return (uidToString unitId);
    when (unitStr nin? noElaboratingMessageFiles)
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
    transformed_spec <- applyOpRefinements compressed_spec;
%    full_spec <- explicateHiddenAxiomsM compressed_spec;
    return (Spec (removeDuplicateImports transformed_spec),TS,depUIDs)
  }
(*
We first evaluate the imports and then the locally declared ops, sorts
axioms, etc.
*)
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
		   | InProcess _ -> 
		     (case (valueOf term) of
			| UnitId (UnitId_Relative   x) -> raise (CircularDefinition x)
			| UnitId (SpecPath_Relative x) -> raise (CircularDefinition x)
			| _ -> raise (Fail ("Circular import")))

		   | _ -> raise (Fail ("Import not a spec")))
		  })
              val               
              (reverse terms) % just so result shows in same order as read
      | _ -> return val

  op  anyImports?: List (SpecElem Position) -> Boolean
  def anyImports? specElems =
    exists? (fn (elem,_) -> case elem of Import _ -> true | _ -> false) specElems

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
		   | Spec impSpec -> mergeImport term impSpec spc position
		   %% Already checked
		   | _ -> raise (Fail ("Shouldn't happen!")))
		  })
              spc               
              terms
      | Sort    (names,       dfn)               -> addSort names      dfn spc position
      | Op      (names, fxty, refine?, dfn)      -> addOp   names fxty refine? dfn spc position

      | Claim   (Axiom,      name, tyVars, term) -> return (addAxiom      ((name,tyVars,term,position), spc)) 
      | Claim   (Theorem,    name, tyVars, term) -> return (addTheorem    ((name,tyVars,term,position), spc))
      | Claim   (Conjecture, name, tyVars, term) -> return (addConjecture ((name,tyVars,term,position), spc))
      | Claim   _                                -> error "evaluateSpecElem: unsupported claim type"

      | Pragma  (prefix, body, postfix)          -> return (addPragma     ((prefix, body, postfix, position), spc))
      | Comment str                              -> return (addComment    (str, position, spc))

  def mergeImport spec_term imported_spec old_spec position =
    let sorts = old_spec.sorts in
    let ops   = old_spec.ops   in
    {
     new_spec  <- return (addImport ((spec_term, imported_spec), old_spec, position));

     new_sorts <- if sorts = emptySpec.sorts then 
                    return imported_spec.sorts
		  else 
		    %% TODO: fold over just infos?
		    foldOverQualifierMap (fn (_, _, info, sorts) ->
					  return (mergeSortInfo new_spec sorts info)) % Which should it be: old_spec, imported_spec, or new_spec ?
		                         sorts 
				         imported_spec.sorts;

     new_ops   <- if ops = emptySpec.ops then 
                    return imported_spec.ops
		  else 
		    %% TODO: fold over just infos?
		    foldOverQualifierMap (fn (_, _, info, ops) ->
					  return (mergeOpInfo new_spec ops info)) % Which should it be: old_spec, imported_spec, or new_spec ?
		                         ops
					 imported_spec.ops;

    return (new_spec << {sorts = new_sorts,
			 ops   = new_ops})
    }

(*
The following wraps the existing \verb+elaborateSpec+ in a monad until
such time as the current one can made monadic.
*)
 op elaborateSpecM : Spec -> SpecCalc.Env Spec
 def elaborateSpecM spc =
   { unitId      <- getCurrentUID;
     filename <- return ((uidToFullPath unitId) ^ ".sw");
     case elaboratePosSpec (spc, filename) of
       | Spec spc    -> return spc
       | Errors msgs -> raise (TypeCheckErrors msgs)
   }

  op explicateHiddenAxiomsM: Spec -> SpecCalc.Env Spec
  def explicateHiddenAxiomsM spc =
    return spc % (explicateHiddenAxioms spc)

  op applyOpRefinements(spc: Spec): SpecCalc.Env Spec =
    foldM (fn spc -> fn elem ->
              case elem of
                | OpDef(qid, refine_num, _) ->
                  % let _ = writeLine("aor0: "^printQualifiedId qid^show refine_num) in
                  (case AnnSpec.findTheOp(spc, qid) of
                   | None -> return spc
                   | Some opinfo ->
                   case unpackNthOpDef(opinfo, refine_num) of
                   | (tvs, ty, dfn) ->
                     (case transformSteps? dfn of
                      | None -> return spc
                      | Some refine_steps ->
                      let all_defs = innerTerms opinfo.dfn in
                      let (_, _, full_tm) = unpackTerm(opinfo.dfn) in
                      let prev_tm = refinedTerm(full_tm, refine_num - 1) in
                      {(_, steps) <- makeScript refine_steps;
                       % print("aor: "^scriptToString(Steps steps)^scriptToString(Steps steps1)^"\n");
                       ((_, tr_term), _) <- interpretTerm(spc, Steps steps, prev_tm, prev_tm, true);
                       new_dfn <- return (maybePiTerm(tvs, SortedTerm (replaceNthTerm(full_tm, refine_num, tr_term),
                                                                       ty, termAnn opinfo.dfn)));
                       return (setOpInfo(spc,qid,opinfo << {dfn = new_dfn}))})
                   | _ -> return spc)
                | _ -> return spc)
       spc spc.elements
     
endspec
