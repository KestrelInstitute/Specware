\subsection{Evalution of a Spec term in the Spec Calculus}

Synchronized with r1.13 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSpec.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import URI/Utilities
  % import ../../../MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/PosSpec
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

\begin{spec}
 def SpecCalc.evaluateSpec spec_elements = 
  %% TODO:  Figure out rules for adding import of Base.
  %%        For example, it should not be imported by specs that it imports.
  %%        And the user might want to suppress auto-import of it.
  %% let spec_elements = 
  %%     if dont_import_base? then
  %%      spec_elements
  %%     else
  %%      let base_path = ["Library","Base","Base"]    in
  %%      let base_uri    : SpecCalc.Term     Position = (URI (SpecPath_Relative base_path), pos0) in
  %%      let base_import : SpecCalc.SpecElem Position = (Import base_uri,                   pos0) in
  %%      let _ = toScreen ("\nAdding import of Base\n") in
  %%      cons(base_import, spec_elements)
  %% in
  {
    (pos_spec,TS,depURIs) <- evaluateSpecElems emptySpec spec_elements;
    elaborated_spec <- elaborateSpecM pos_spec;
    return (Spec elaborated_spec,TS,depURIs)
  }
\end{spec}

\begin{spec}
  op evaluateSpecElems : ASpec Position -> List (SpecElem Position)
                           -> Env (ASpec Position * TimeStamp * URI_Dependency)
  def evaluateSpecElems initialSpec specElems =
     %% Get import information first
     {(spcWithImports,TS,depURIs)
        <- foldM evaluateSpecImport (initialSpec,0,[]) specElems;
      fullSpec <- foldM evaluateSpecElem spcWithImports specElems;
      return (fullSpec,TS,depURIs)}

  op evaluateSpecImport : (ASpec Position * TimeStamp * URI_Dependency)
                          -> SpecElem Position
                          -> Env (ASpec Position * TimeStamp * URI_Dependency)
  def evaluateSpecImport (val as (spc,cTS,cDepURIs)) (elem, _(* position *)) =
    case elem of
      | Import term -> {
            (value,iTS,depURIs) <- evaluateTermInfo term;
            (case value of
              | Spec impSpec ->
                 return (mergeImport ((term, impSpec), spc),
			 max(cTS,iTS), cDepURIs ++ depURIs)
                  %% return (extendImports spc impSpec) 
              | _ -> raise(Fail("Import not a spec")))
          }
      | _ -> return val

  op evaluateSpecElem : ASpec Position
                          -> SpecElem Position
                          -> Env (ASpec Position)
  def evaluateSpecElem spc (elem, _(* position *)) =
    case elem of
      | Import term -> return spc
      | Sort (name,(tyVars,optSort)) ->
          return (addPSort ((name, tyVars, optSort), spc))
      | Op (name,(fxty,srtScheme,optTerm)) ->
          return (addPOp ((name, fxty, srtScheme, optTerm), spc))
      | Claim (Axiom, name, tyVars, term) ->
          return (addAxiom ((name,tyVars,term), spc)) 
      | Claim (Theorem, name, tyVars, term) ->
          return (addTheorem ((name,tyVars,term), spc))
      | Claim (Conjecture, name, tyVars, term) ->
          return (addConjecture ((name,tyVars,term), spc))
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"

 def mergeImport ((spec_term, imported_spec), spec_a) =
   let spec_b = addImport ((showTerm spec_term, imported_spec), spec_a) in
   let spec_c = setSorts
                  (spec_b,
		   foldriAQualifierMap
		     (fn (imported_qualifier, 
			  imported_id, 
			  imported_sort_info, 
			  combined_psorts) ->
		      let newPSortInfo = convertSortInfoToPSortInfo imported_sort_info in
		      let oldPSortInfo = findAQualifierMap(combined_psorts,imported_qualifier,
							   imported_id) in
		      insertAQualifierMap(combined_psorts,
					  imported_qualifier,
					  imported_id,
					  mergePSortInfo(newPSortInfo,oldPSortInfo,
							 imported_qualifier,imported_id)))
		     spec_b.sorts
		     imported_spec.sorts)
   in
   let spec_d = setOps(spec_c,
                       foldriAQualifierMap
		         (fn (imported_qualifier, 
			      imported_id, 
			      imported_op_info, 
			      combined_pops) ->
			  let newPOpInfo = convertOpInfoToPOpInfo imported_op_info in
			  let oldPOpInfo = findAQualifierMap(combined_pops,imported_qualifier,
							     imported_id) in
			  insertAQualifierMap(combined_pops,
					      imported_qualifier,
					      imported_id,
					      mergePOpInfo(newPOpInfo,oldPOpInfo,
							   imported_qualifier,imported_id)))
			 spec_c.ops
			 imported_spec.ops)
   in
     spec_d

\end{spec}

The following wraps the existing \verb+elaborateSpec+ in a monad until
such time as the current one can made monadic.

\begin{spec}
 op elaborateSpecM : PosSpec -> Env Spec
 def elaborateSpecM spc =
   {
     uri <- getCurrentURI;
     case elaboratePosSpec (spc, (uriToPath uri) ^ ".sw", true) of
       | Ok pos_spec -> return (convertPosSpecToSpec pos_spec)
       | Error msg   -> raise  (OldTypeCheck msg)
   }
\end{spec}

\begin{spec}
}
\end{spec}
