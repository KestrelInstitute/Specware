\subsection{Spec Translation}

Synchronized with r1.4 Languages/SpecCalculus/Semantics/Evaluate/EvalSpecMorphism.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import ../../../MetaSlang/Specs/StandardSpec
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
  def translateSpec spc expr = 
      return (auxTranslateSpec(spc,makeTranslationMaps(spc,expr)))
    
  op makeTranslationMaps :
      Spec
    * (TranslateExpr Position)
    -> AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId)
  %% Need to change fail to raise
  def makeTranslationMaps(spc,(transPairs,_)) =
    let def insert(((n as Qualified(qualifier,id),m),pos),(opMap,sortMap)) =
          case findAllOps(spc,n) of
             | ((Qualified(qualifiern,idn))::_,_,_,_)::rs ->
                 (if rs = [] then
                    ()
                  else
                    fail ("translate: Ambiguous source op name "^qualifier^"."^id);
                 (insertAQualifierMap(opMap,qualifiern,idn,m),sortMap))
             | _ ->
                (case findAllSorts(spc,n) of
                   | ((Qualified(qualifiern,idn))::_,_,_)::rs  ->
                       (if rs = [] then
                          ()
                        else
                          fail("translate: Ambiguous source op name "^qualifier^"."^id);
                       (opMap,insertAQualifierMap(sortMap,qualifiern,idn,m)))
                   | _ -> System.fail ("Translate: Identifier \""^qualifier^"."^id^
                                 "\" has not been defined."))
    in
       List.foldr insert (emptyAQualifierMap,emptyAQualifierMap) transPairs

 % Make a monad when debugged
 op auxTranslateSpec : Spec * (AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId))
                     -> Spec
 def auxTranslateSpec (spc, (opMap,sortMap)) =
  %% Change UnQualified to new_qualifier in all qualified names
  let
    def translateQualifiedId (idMap,qid as Qualified (qualifier, id)) =
      case findAQualifierMap(idMap,qualifier,id)
        of Some nQId -> nQId
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
      foldriAQualifierMap (fn (qualifier, id, (aliases, x, y, optional_def),newMap) ->
                           %% TODO:
                           %% If qualifier = UnQualified and new_qualifier.id
                           %% already in map then should check for consistency
                           let qual as Qualified(r_qualifier,r_id)
                              = translateQualifiedId(opMap,Qualified (qualifier, id))
                           in
                           insertAQualifierMap
                             (newMap, r_qualifier, r_id,
                              ([qual], x, y, optional_def)))
        emptyAQualifierMap ops

    def translateSortMap sorts =
      foldriAQualifierMap (fn (qualifier, id, (aliases, ty_vars, optional_def),
                               newMap) ->
                           %% TODO:
                           %% If qualifier = UnQualified and new_qualifier.id
                           %% already in map then should check for consistency
                            let qual as Qualified(r_qualifier,r_id)
                              = translateQualifiedId(sortMap,Qualified (qualifier, id))
                           in
                           insertAQualifierMap
                             (newMap, r_qualifier, r_id,
                              ([qual], ty_vars, optional_def)))
        emptyAQualifierMap sorts

    def translateSpec sp =
     let {importInfo = _, sorts, ops, properties}
         = mapSpec (translateOp, translateSort, translatePattern) sp
     %%         importedSpecs    = mapImports translateSpec importedSpecs
     in
       {importInfo   = emptyImportInfo,        % Could change if we get smarter
        sorts        = translateSortMap sorts,
        ops          = translateOpMap   ops,
        properties   = properties}

  in
  translateSpec spc
}
\end{spec}
