\subsection{Evalution of a Spec term in the Spec Calculus}

Synchronized with r1.13 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSpec.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import URI/Utilities
  % import ../../../MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Transformations/DefToAxiom
  import Spec/Utilities
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion

  sort Env a = SpecCalc.Env a

\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

\begin{spec}
 def SpecCalc.evaluateSpec spec_elements position = {
    uri <- getCurrentURI;
    print (";;; Processing spec at "^(uriToString uri)^"\n");
    (pos_spec,TS,depURIs) <- evaluateSpecElems emptySpec spec_elements;
    elaborated_spec <- elaborateSpecM pos_spec;
    compressed_spec <- complainIfAmbiguous (compressDefs elaborated_spec) position;
%    full_spec <- explicateHiddenAxiomsM compressed_spec;
    return (Spec compressed_spec,TS,depURIs)
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
            (case coerceToSpec value of
              | Spec impSpec -> {
                    newSpc <- mergeImport term impSpec spc position;
                    return (newSpc, max(cTS,iTS), listUnion(cDepURIs,depURIs))
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

 op elaborateSpecM : Spec -> Env Spec
 def elaborateSpecM spc =
   { uri      <- getCurrentURI;
     filename <- return ((uriToFullPath uri) ^ ".sw");
     %% No longer necessary
     %% hackMemory ();
     case elaboratePosSpec (spc, filename) of
       | Spec spc    -> return spc
       | Errors msgs -> raise (TypeCheckErrors msgs)
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

\end{spec}

\begin{spec}
  op explicateHiddenAxiomsM: Spec -> Env Spec
  def explicateHiddenAxiomsM spc =
    return spc % (explicateHiddenAxioms spc)

}
\end{spec}
