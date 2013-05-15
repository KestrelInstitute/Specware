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
  import Transform, Qualify

(*
To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.
*)

 op  noElaboratingMessageFiles: List String
 def noElaboratingMessageFiles = []

 def SpecCalc.evaluateSpec (spec_elements: ExplicitSpecTerm) (defaultQual: Id) (position: Position) = {
    unitId <- getCurrentUID;
    unitStr <- return (uidToString unitId);
    when (unitStr nin? noElaboratingMessageFiles)
       (print (";;; Elaborating spec at " ^ unitStr ^ "\n"));
    (optBaseUnitId,baseSpec) <- getBase;
    (pos_spec,TS,depUIDs) <-
      evaluateSpecElems
	(markQualified % even the empty spec!
	   (if anyImports? spec_elements
              then emptySpec % some import will include baseSpec
            else importOfSpec(optBaseUnitId,baseSpec))
           defaultQual)
	spec_elements;
    elaborated_spec <- elaborateSpecM pos_spec;
    elaborated_spec <- complainIfAmbiguous elaborated_spec position;
%    compressed_spec <- complainIfAmbiguous (compressDefs elaborated_spec) position;
%    print(printSpec compressed_spec);
    transformed_spec <- applyOpRefinements elaborated_spec;  % compressed_spec;
    return (Spec (markQualifiedStatus(removeDuplicateImports transformed_spec)),
            TS,depUIDs)
  }
(*
We first evaluate the imports and then the locally declared ops, types
axioms, etc.
*)
  op evaluateSpecElems : Spec -> SpecElemTerms -> SpecCalc.Env (Spec * TimeStamp * UnitId_Dependency)
  def evaluateSpecElems starting_spec specElems = {
      %% Use the name starting_spec to avoid any possible confusion with the
      %% op initialSpecInCat, which refers to the initial spec in the category of specs.
      (TS, depUIDs, imports_info) <- foldM checkImports (0,[],[]) specElems;
      imports_spc <- foldM doImport starting_spec imports_info;
      fullSpec <- foldM evaluateSpecElem imports_spc specElems;
      return (fullSpec,TS,depUIDs)
    }

  op  checkImports : (TimeStamp * UnitId_Dependency * List(SCTerm * Spec * Position))
                    -> SpecElemTerm
                    -> SpecCalc.Env (TimeStamp
                                      * UnitId_Dependency
                                      * List(SCTerm * Spec * Position))
  def checkImports val (elem, position) =
    case elem of
      | Import terms -> 
        foldM (fn (cTS, cDepUIDs, imports_info) -> fn term ->
	       {
		(value,iTS,depUIDs) <- evaluateTermInfo term;
		(case coerceToSpec value of
		   | Spec spc -> return (max(cTS,iTS), listUnion(cDepUIDs,depUIDs),
                                         (term, spc, position)::imports_info)
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

  op  anyImports?: SpecElemTerms -> Bool
  def anyImports? specElems =
    exists? (fn (elem,_) -> case elem of Import _ -> true | _ -> false) specElems

  op doImport(spc: Spec) (term: SCTerm, impSpec: Spec, position: Position): SpecCalc.Env Spec =
   {(term, impSpec)
      <- if ~(qualifiedSpec? impSpec) && qualifiedSpec?(spc)
           then let Some qual = spc.qualifier in
                {impSpec <- qualifySpec impSpec qual [] position;
                 % print("Implicit "^qual^" qualifying "^showSCTerm term^"\n");
                 return ((Qualify (term, qual), noPos), impSpec)}
         else return (term, impSpec);
    mergeImport term impSpec spc position}

  op evaluateSpecElem : Spec -> SpecElemTerm -> SpecCalc.Env Spec
  def evaluateSpecElem spc (elem, position) =
    case elem of
      | Import terms -> return spc      % Already done
      | Type    (names,       dfn)               -> addType names      dfn spc position
      | Op      (names, fxty, refine?, dfn)      -> addOp   names fxty refine? dfn spc position

      | Claim   (Axiom,      name, tyVars, term) -> return (addAxiom      ((addQualifier spc name,tyVars,term,position), spc)) 
      | Claim   (Theorem,    name, tyVars, term) -> return (addTheorem    ((addQualifier spc name,tyVars,term,position), spc))
      | Claim   (Conjecture, name, tyVars, term) -> return (addConjecture ((addQualifier spc name,tyVars,term,position), spc))
      | Claim   _                                -> SpecCalc.error "evaluateSpecElem: unsupported claim type"

      | Pragma  (prefix, body, postfix)          -> return (addPragma     ((prefix, body, postfix, position), spc))
      | Comment str                              -> return (addComment    (str, position, spc))

  def SpecCalc.mergeImport spec_term imported_spec old_spec position =
    let types = old_spec.types in
    let ops   = old_spec.ops   in
    {
     new_spec  <- return (addImport ((spec_term, imported_spec), old_spec, position));

     new_types <- if types = emptySpec.types then 
                    return imported_spec.types
		  else 
		    %% TODO: fold over just infos?
		    foldOverQualifierMap (fn (_, _, info, types) ->
					  return (mergeTypeInfo new_spec types info)) % Which should it be: old_spec, imported_spec, or new_spec ?
		                         types 
				         imported_spec.types;

     new_ops   <- if ops = emptySpec.ops then 
                    return imported_spec.ops
		  else 
		    %% TODO: fold over just infos?
		    foldOverQualifierMap (fn (_, _, info, ops) ->
					  return (mergeOpInfo new_spec ops info)) % Which should it be: old_spec, imported_spec, or new_spec ?
		                         ops
					 imported_spec.ops;

    return (new_spec << {types = new_types,
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
                | OpDef(qid, refine_num, _, _) | refine_num > 0 ->
                  % let _ = writeLine("aor0: "^printQualifiedId qid^show refine_num) in
                  (case findTheOp(spc, qid) of
                   | None -> return spc
                   | Some opinfo ->
                   let trps = unpackTypedTerms (opinfo.dfn) in
                   let (tvs, ty, dfn) = nthRefinement(trps, refine_num) in
                   (case transformSteps? dfn of
                      | None -> return spc
                      | Some refine_steps ->
                        let (_, _, prev_tm) = nthRefinement(trps, refine_num - 1) in
                        {steps <- mapM makeScript refine_steps;
                         % print("aor: "^scriptToString(Steps steps)^scriptToString(Steps steps1)^"\n");
                         (tr_term, _, hist) <- interpretTerm(spc, Steps steps, prev_tm, ty, qid, false, []);
                         new_dfn <- return (maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, tr_term))));
                         return (setOpInfo(spc,qid,opinfo << {dfn = new_dfn}))})
                   | _ -> return spc)
                | _ -> return spc)
       spc spc.elements
     
end-spec
