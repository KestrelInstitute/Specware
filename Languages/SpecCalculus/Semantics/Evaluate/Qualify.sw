\subsection{Name Qualifing in Specs}

Synchronized with r1.9 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalTerm.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import Spec/Utilities
\end{spec}

To qualify a spec means to change all unqualified names to qualified
names. This can raise exceptions since qualifying a name may identify
it with a name that already exists.

The current version need not visit the imported specs as the hierarchy
is flattened,

Change UnQualified to new_qualifier in all qualified names

\begin{spec} 
  def SpecCalc.evaluateQualify term new_qualifier = {
       (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
        case coerceToSpec value of
          | Spec spc -> {
                qualified_spec <- qualifySpec spc new_qualifier (positionOf term);
                return (Spec qualified_spec,timeStamp,depURIs)
              }
          | _ -> raise (TypeCheck ((positionOf term),
                            "qualifying a term that is not a specification"))
    }

  op qualifySpec : Spec -> Qualifier -> Position -> SpecCalc.Env Spec
  def qualifySpec spc new_qualifier position =
    let
      def translateQualifiedId (qid as Qualified (qualifier, id)) =
        if qualifier = UnQualified then
          Qualified (new_qualifier, id)
        else 
          qid
  
      def translateOp op_term =
        case op_term of
         | Fun (Op (qid, fixity), srt, a) ->
           let new_qid = translateQualifiedId qid in
           if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
         | _ -> op_term
  
      def translateSort sort_term =
        case sort_term of
         | Base (qid, srts, a) ->
           let new_qid = translateQualifiedId qid in
           if new_qid = qid then sort_term else Base (new_qid, srts, a)
         | _ -> sort_term
  
      def translatePattern pat = pat
  
      def convertOpMap opMap =
        let def qualifyStep (qualifier, id, (aliases, x, y, optional_def),newMap) =
          let newOpInfo = (map translateQualifiedId aliases, x, y, optional_def) in
          let newQualifier =
            if qualifier = UnQualified then
              new_qualifier
            else
              qualifier in
          let oldOpInfo = findAQualifierMap (newMap, newQualifier, id) in {
              opInfo <- mergeOpInfo newOpInfo oldOpInfo newQualifier id position;
              %% Possibly the new name already is used
              return (insertAQualifierMap (newMap, newQualifier, id, opInfo))
            } in
        foldOverQualifierMap qualifyStep emptyAQualifierMap opMap 
  
      def convertSortMap sortMap =
        let def qualifyStep (qualifier, id, (aliases, ty_vars, optional_def), newMap) =
          let newSortInfo = (map translateQualifiedId aliases, ty_vars, optional_def) in
          let newQualifier =
            if qualifier = UnQualified then
              new_qualifier
            else
              qualifier in
          let oldSortInfo = findAQualifierMap (newMap, newQualifier, id) in {
              sortInfo <- mergeSortInfo newSortInfo oldSortInfo newQualifier id position; 
              %% Possibly the new name already is used
              return (insertAQualifierMap (newMap, newQualifier, id, sortInfo))
            } in
        foldOverQualifierMap qualifyStep emptyAQualifierMap sortMap
  
      def convertSpec sp =
       let {importInfo = {imports,importedSpec,localOps,localSorts}, sorts, ops, properties}
           = mapSpec (translateOp, translateSort, translatePattern) sp
       %%         importedSpecs    = mapImports convertSpec importedSpecs
       in {
         newSorts <- convertSortMap sorts;
         newOps <- convertOpMap ops;
         return {
            importInfo = {
              imports = imports,
              importedSpec = importedSpec,
              localOps = map translateQualifiedId localOps,
              localSorts = map translateQualifiedId localSorts
            },  
            sorts      = newSorts,
            ops        = newOps,
            properties = properties
         }
       }
    in convertSpec spc
}
\end{spec}
