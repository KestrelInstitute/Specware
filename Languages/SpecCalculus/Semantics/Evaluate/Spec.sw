\subsection{Evalution of a Spec term in the Spec Calculus}

Synchronized with r1.13 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSpec.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import URI/Utilities
  % import ../../../MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import Spec/Utilities
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
  %%      let base_uri    : SpecCalc.Term     Position = (URI (SpecPath_Relative base_path), Internal) in
  %%      let base_import : SpecCalc.SpecElem Position = (Import base_uri,                   Internal) in
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
     {(spcWithImports0,TS,depURIs)
        <- foldM evaluateSpecImport (initialSpec,0,[]) specElems;
      spcWithImports <- maybeAddBaseImport(spcWithImports0,initialSpec);
      fullSpec <- foldM evaluateSpecElem spcWithImports specElems;
      return (fullSpec,TS,depURIs)}

  op evaluateSpecImport : (ASpec Position * TimeStamp * URI_Dependency)
                          -> SpecElem Position
                          -> Env (ASpec Position * TimeStamp * URI_Dependency)
  def evaluateSpecImport (val as (spc,cTS,cDepURIs)) (elem, position) =
    case elem of
      | Import term -> {
            (value,iTS,depURIs) <- evaluateTermInfo term;
            (case value of
              | Spec impSpec -> {
                    newSpc <- mergeImport term impSpec spc position;
                    return (newSpc, max(cTS,iTS), cDepURIs ++ depURIs)
                  }
              | _ -> raise (Fail ("Import not a spec")))
          }
      | _ -> return val

  op evaluateSpecElem : ASpec Position
                          -> SpecElem Position
                          -> Env (ASpec Position)
  def evaluateSpecElem spc (elem, position) =
    case elem of
      | Import term -> return spc
      | Sort (names,(tyVars,optSort)) ->
          addSort names tyVars optSort spc position
      | Op (names,(fxty,srtScheme,optTerm)) ->
          addOp names fxty srtScheme optTerm spc position
      | Claim (Axiom, name, tyVars, term) ->
          return (addAxiom ((name,tyVars,term), spc)) 
      | Claim (Theorem, name, tyVars, term) ->
          return (addTheorem ((name,tyVars,term), spc))
      | Claim (Conjecture, name, tyVars, term) ->
          return (addConjecture ((name,tyVars,term), spc))
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"

  def mergeImport spec_term imported_spec spec_a position =
    let def mergeSortStep (imported_qualifier, imported_id, imported_sort_info, combined_psorts) =
      let newPSortInfo = convertSortInfoToPSortInfo imported_sort_info in
      let oldPSortInfo = findAQualifierMap (combined_psorts,imported_qualifier, imported_id) in {
          mergedSorts <- SpecCalc.mergeSortInfo newPSortInfo oldPSortInfo imported_qualifier imported_id position;
          return (insertAQualifierMap (combined_psorts,
                                       imported_qualifier,
                                       imported_id,
                                       mergedSorts))
        } in
    let def mergeOpStep (imported_qualifier, imported_id, imported_op_info, combined_pops) =
      let newPOpInfo = convertOpInfoToPOpInfo imported_op_info in
      let oldPOpInfo = findAQualifierMap (combined_pops,imported_qualifier, imported_id) in {
           mergedOps <- SpecCalc.mergeOpInfo newPOpInfo oldPOpInfo imported_qualifier imported_id position;
           return (insertAQualifierMap (combined_pops,
                                        imported_qualifier,
                                        imported_id,
                                        mergedOps))
        } in
    {
      spec_b <- return (addImport ((showTerm spec_term, imported_spec), spec_a)); 
      sorts_b <- foldOverQualifierMap mergeSortStep spec_b.sorts imported_spec.sorts;
      spec_c <- return (setSorts (spec_b, sorts_b));
      ops_c <- foldOverQualifierMap mergeOpStep spec_c.ops imported_spec.ops;
      spec_d <- return (setOps(spec_c, ops_c));
      return spec_d
    }
\end{spec}

The following wraps the existing \verb+elaborateSpec+ in a monad until
such time as the current one can made monadic.

\begin{spec}
 op elaborateSpecM : PosSpec -> Env Spec
 def elaborateSpecM spc =
   { uri      <- getCurrentURI;
     filename <- return ((uriToPath uri) ^ ".sw");
     print (";;; Processing spec "
			^ (case uri.hashSuffix of
			     | Some nm -> nm ^ " "
			     | _ -> "")
			^ "in "
            ^ filename
            ^ "\n");
     case elaboratePosSpec (spc, filename) of
       | Ok pos_spec -> return (convertPosSpecToSpec pos_spec)
       | Error msg   -> raise  (OldTypeCheck msg)
   }
\end{spec}

A first attempt at adding implicit import of Base spec. Assumes
/Library/Base/Base is in the spec path, and doesn't do implicit import
of there are explicit imports or the spec is in a directory that ends in
/Libary/Base/ .

\begin{spec}
  op maybeAddBaseImport : ASpec Position * ASpec Position -> Env (ASpec Position)
  def maybeAddBaseImport (spc, initialSpec) =
    if ~(spc = initialSpec) then return spc       % should already include Base
     else
       {uri <- getCurrentURI;
        if baseSpecURI? uri then return spc       % used when defining base
        else {(Spec baseSpec,_,_)
                <- SpecCalc.evaluateURI (Internal "adding base import")
                     (SpecPath_Relative {path = ["Library","Base"],
                                         hashSuffix = None});
              return (convertSpecToPosSpec baseSpec)}}

 % op aBaseSpec? : URI * ASpec Position -> Boolean
 op baseSpecURI? : URI -> Boolean
 def baseSpecURI? uri =
   case uri of
     | {path, hashSuffix = None} -> baseSpecPath? path
     | _ -> false
  
 def baseSpecPath? path =
   case path of
     | []                   -> false
     | [_]                  -> false
     | ["Library","Base"]   -> true
     | [_,_]                -> false
     | ["Library","Base",_] -> true
     | _::r                 -> baseSpecPath? r
}
\end{spec}
