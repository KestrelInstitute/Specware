\subsection{Spec Translation}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import ../../../MetaSlang/Specs/StandardSpec
  import Spec/Utilities
\end{spec}

Perhaps evaluating a translation should yield a morphism rather than just 
a spec. Then perhaps we add dom and cod domain operations on morphisms.
Perhaps the calculus is getting too complicated.

\begin{spec}
  op evaluateTranslate :
       SpecCalc.Term Position
    -> TranslateExpr Position
    -> Env ValueInfo
  def evaluateTranslate term translation = {
      (value,timeStamp,depURIs) <- evaluateTermInfo term;
      case value of
        | Spec spc -> {
              spcTrans <- translateSpec spc translation;
              return (Spec spcTrans,timeStamp,depURIs)
            }
        | _ -> raise (TypeCheck (positionOf term,
                         "translating a term that is not a specification"))
    }
\end{spec}

To translate a spec means to recursively descend the hierarchy of imports
and translate names. This can raise exceptions since ops may end up with
the same names.

\begin{spec}
  op translateSpec : Spec -> TranslateExpr Position -> Env Spec
  def translateSpec spc expr = {
      transMaps <- makeTranslationMaps spc expr;
      auxTranslateSpec spc transMaps (positionOf expr)
    } 
    
  op makeTranslationMaps :
        Spec
     -> TranslateExpr Position
     -> SpecCalc.Env (AQualifierMap QualifiedId * AQualifierMap QualifiedId)
  def makeTranslationMaps spc (transPairs,position) =
    let def insert (opMap,sortMap) ((n as Qualified(qualifier_n,id_n),Qualified(qualifier_m,id_m)),pos) =
          case findAllOps(spc,n) of
            | ((Qualified(qualifierN,idN))::_,_,_,_)::rs ->
                if rs = [] or qualifierN = UnQualified then 
                  return (insertAQualifierMap(opMap,qualifierN,idN,
                                     Qualified(if qualifier_m = UnQualified
                                                then qualifierN
                                                else qualifier_m,
                                               id_m)),
                  sortMap)
                else
                  raise (SpecError (position, "translate: Ambiguous source op name: "^id_n))
             | _ ->
                (case findAllSorts(spc,n) of
                   | ((Qualified(qualifierN,idN))::_,_,_)::rs  ->
                       if rs = [] or qualifierN = UnQualified then
                         return (opMap,insertAQualifierMap(sortMap,qualifierN,idN,
                                           Qualified(if qualifier_m = UnQualified
                                                        then qualifierN
                                                       else qualifier_m,
                                                     id_m)))
                       else
                         raise (SpecError (position, "translate: Ambiguous source sort name: "^id_n))
                   | _ -> raise (SpecError (position, "translate: Identifier \""^qualifier_n^"."^id_m^ "\" not found.")))
    in
       foldM insert (emptyAQualifierMap,emptyAQualifierMap) transPairs

  op auxTranslateSpec :
        Spec 
     -> (AQualifierMap QualifiedId * AQualifierMap QualifiedId)
     -> Position
     -> SpecCalc.Env Spec
  def auxTranslateSpec spc (opMap,sortMap) position =
    %% Change UnQualified to new_qualifier in all qualified names
    let
      def translateQualifiedId (idMap,qid as Qualified (qualifier, id)) =
        case findAQualifierMap (idMap,qualifier,id) of
          | Some nQId -> nQId
          | None -> qid
  
      def translateOp op_term =
        case op_term of
          | Fun (Op (qid, fixity), srt, a) ->
            let new_qid = translateQualifiedId (opMap,qid) in
            if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
          | _ -> op_term

      def translateSort sort_term =
        case sort_term of
          | Base (qid, srts, a) ->
             let new_qid = translateQualifiedId (sortMap,qid) in
             if new_qid = qid then sort_term else Base (new_qid, srts, a)
          | _ -> sort_term

      def translatePattern pat = pat

      def translateOpMap ops =
        let def translateStep (qualifier, id, (aliases, x, y, optional_def),newMap) =
          let qual as Qualified (new_qualifier,new_id)
               = translateQualifiedId (opMap,Qualified (qualifier, id)) in
          let newOpInfo = ([qual], x, y, optional_def) in
          let oldOpInfo = findAQualifierMap (newMap, new_qualifier, new_id) in {
              opInfo <- mergeOpInfo newOpInfo oldOpInfo new_qualifier new_id position;
              return (insertAQualifierMap (newMap, new_qualifier, new_id, opInfo))
            } in
        foldOverQualifierMap translateStep emptyAQualifierMap ops 

      def translateSortMap sorts =
        let def translateStep (qualifier, id, (aliases, ty_vars, optional_def), newMap) =
           let qual as Qualified(new_qualifier,new_id)
              = translateQualifiedId(sortMap,Qualified (qualifier, id)) in
           let newSortInfo = ([qual], ty_vars, optional_def) in
           let oldSortInfo = findAQualifierMap(newMap, new_qualifier, new_id) in {
               sortInfo <- mergeSortInfo newSortInfo oldSortInfo new_qualifier new_id position;
               return (insertAQualifierMap (newMap, new_qualifier, new_id, sortInfo))
             } in
        foldOverQualifierMap translateStep emptyAQualifierMap sorts 

    in
    let {importInfo = _, sorts, ops, properties}
         = mapSpec (translateOp, translateSort, translatePattern) spc
     %%         importedSpecs    = mapImports translateSpec importedSpecs
    in {
      newSorts <- translateSortMap sorts;
      newOps <- translateOpMap ops;
      return {
          importInfo = emptyImportInfo,        % Could change if we get smarter
          sorts      = newSorts,
          ops        = newOps,
          properties = properties
        }
    }
}
\end{spec}
