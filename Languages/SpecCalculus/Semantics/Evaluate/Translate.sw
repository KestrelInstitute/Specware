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
    Spec * (TranslateExpr Position)
      -> AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId)
  %% Need to change fail to raise
 def makeTranslationMaps(spc,(transPairs,_)) =
    let def insert(((n as Qualified(qualifier_n,id_n),Qualified(qualifier_m,id_m)),pos),
		   (opMap,sortMap)) =
	  case findAllOps(spc,n)
	    of ((Qualified(qualifierN,idN))::_,_,_,_)::rs ->
	       (if rs = [] or qualifierN = UnQualified then ()
		 else fail("translate: Ambiguous source op name: "^id_n);
	        (insertAQualifierMap(opMap,qualifierN,idN,
				     Qualified(if qualifier_m = UnQualified
					        then qualifierN
						else qualifier_m,
					       id_m)),
		 sortMap))
	     | _ ->
	  (case findAllSorts(spc,n)
	    of ((Qualified(qualifierN,idN))::_,_,_)::rs  ->
	       (if rs = [] or qualifierN = UnQualified then ()
		 else fail("translate: Ambiguous source sort name: "^id_n);
		(opMap,insertAQualifierMap(sortMap,qualifierN,idN,
					   Qualified(if qualifier_m = UnQualified
						        then qualifierN
						       else qualifier_m,
						     id_m))))
	     | _ -> fail ("Translate: Identifier \""^qualifier_n^"."^id_m^ "\" not found."))
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
      foldriAQualifierMap
        (fn (qualifier, id, (aliases, x, y, optional_def),newMap) ->
	   let qual as Qualified(new_qualifier,new_id)
	      = translateQualifiedId(opMap,Qualified (qualifier, id))
	   in
	   let newOpInfo = ([qual], x, y, optional_def) in
	   let oldOpInfo = findAQualifierMap(newMap, new_qualifier, new_id) in
	   insertAQualifierMap
	     (newMap, new_qualifier, new_id,
	      mergeOpInfo(newOpInfo, oldOpInfo, new_qualifier, new_id)))
        emptyAQualifierMap ops

    def translateSortMap sorts =
      foldriAQualifierMap
        (fn (qualifier, id, (aliases, ty_vars, optional_def),
	     newMap) ->
	 let qual as Qualified(new_qualifier,new_id)
	    = translateQualifiedId(sortMap,Qualified (qualifier, id))
	 in
	 let newSortInfo = ([qual], ty_vars, optional_def) in
	   let oldSortInfo = findAQualifierMap(newMap, new_qualifier, new_id) in
	   insertAQualifierMap
	   (newMap, new_qualifier, new_id,
	    mergeSortInfo(newSortInfo, oldSortInfo, new_qualifier, new_id)))
        emptyAQualifierMap sorts

  in
  let {importInfo = _, sorts, ops, properties}
         = mapSpec (translateOp, translateSort, translatePattern) spc
     %%         importedSpecs    = mapImports translateSpec importedSpecs
  in
    {importInfo   = emptyImportInfo,	% Could change if we get smarter
     sorts        = translateSortMap sorts,
     ops          = translateOpMap   ops,
     properties   = properties}

}
\end{spec}
