\subsection{Name Qualifing in Specs}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
\end{spec}

To qualify a spec means to change all unqualified names to qualified
names. This can raise exceptions since qualifying a name may identify
it with a name that already exists.

The current version need not visit the imported specs as the hierarchy
is flattened,

\begin{spec} 
  def SpecCalc.qualifySpec spc qualifier = 
     return (let qSpec = auxQualifySpec (spc, qualifier) in qSpec)

 % Make a monad when debugged
 op auxQualifySpec : Spec * Qualifier -> Spec
 def auxQualifySpec (spc, new_qualifier) =
  %% Change UnQualified to new_qualifier in all qualified names
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
      foldriAQualifierMap (fn (qualifier, id, (aliases, x, y, optional_def),newMap) ->
                           %% TODO:
                           %% If qualifier = UnQualified and new_qualifier.id
                           %% already in map then should check for consistency
                           insertAQualifierMap
                             (newMap,
                              if qualifier = UnQualified
                                then new_qualifier
                                else qualifier,
                              id,
                              (map translateQualifiedId aliases, x, y, optional_def)))
        emptyAQualifierMap opMap

    def convertSortMap sortMap =
      foldriAQualifierMap (fn (qualifier, id, (aliases, ty_vars, optional_def), newMap) ->
                           %% TODO:
                           %% If qualifier = UnQualified and new_qualifier.id
                           %% already in map then should check for consistency
                           insertAQualifierMap
                             (newMap, 
                              if qualifier = UnQualified
                                then new_qualifier
                                else qualifier,
                              id,
                              (map translateQualifiedId aliases, ty_vars, optional_def)))
        emptyAQualifierMap sortMap

    def convertSpec sp =
     let {imports, importedSpec, sorts, ops, properties}
         = mapSpec (translateOp, translateSort, translatePattern) sp
     %%         importedSpecs    = mapImports convertSpec importedSpecs
     in
       {imports      = imports,
        importedSpec = importedSpec,  
        sorts        = convertSortMap sorts,
        ops          = convertOpMap   ops,
        properties   = properties}

  in
  convertSpec spc
}
\end{spec}
