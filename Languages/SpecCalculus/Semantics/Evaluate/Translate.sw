\subsection{Spec Translation}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
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
  def makeTranslationMaps dom_spec (translation_pairs, position) =
    let def insert (translation_opmap, translation_sortmap) 
                   ((dom_qid as Qualified (dom_qualifier, dom_id), Qualified (target_qualifier, target_id)), 
		    pos) 
          =
          %% TODO:  What if dom_qid names both an op and a sort ??  Right now, we translate the op but not the sort.
          case findAllOps (dom_spec, dom_qid) of
            | _::other_opinfos ->
                if other_opinfos = [] then % or qualifier_from_op_info = UnQualified then 
                  return (insertAQualifierMap (translation_opmap, dom_qualifier, dom_id,
					       Qualified (if target_qualifier = UnQualified
							    then dom_qualifier
							  else target_qualifier,
							 target_id)),
                          translation_sortmap)
                else
                  raise (SpecError (position, "translate: Ambiguous source op name: "^ dom_id))
             | _ ->
                (case findAllSorts (dom_spec, dom_qid) of
                   | _::other_sortinfos ->
                     if other_sortinfos = [] then % or qualifier_from_sort_info = UnQualified then 
		       return (translation_opmap,
			       insertAQualifierMap (translation_sortmap, dom_qualifier, dom_id,
						    Qualified (if target_qualifier = UnQualified
								 then dom_qualifier
							       else target_qualifier,
							       target_id)))
		     else
		       raise (SpecError (position, "translate: Ambiguous source sort name: "^dom_id))
                   | _ -> raise (SpecError (position, "translate: Identifier \""^dom_qualifier^"."^dom_id^ "\" not found.")))
    in
       foldM insert (emptyAQualifierMap, emptyAQualifierMap) translation_pairs

  op auxTranslateSpec :
        Spec 
     -> (AQualifierMap QualifiedId * AQualifierMap QualifiedId)
     -> Position
     -> SpecCalc.Env Spec
  def auxTranslateSpec spc (op_id_map, sort_id_map) position =
    %% Change UnQualified to new_qualifier in all qualified names
    let
      def translateQualifiedId (id_map, qid as Qualified (qualifier, id)) =
        case findAQualifierMap (id_map, qualifier,id) of
          | Some nQId -> nQId
          | None -> qid
  
      def translateOp op_term =
        case op_term of
          | Fun (Op (qid, fixity), srt, a) ->
            let new_qid = translateQualifiedId (op_id_map, qid) in
            if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
          | _ -> op_term

      def translateSort sort_term =
        case sort_term of
          | Base (qid, srts, a) ->
             let new_qid = translateQualifiedId (sort_id_map, qid) in
             if new_qid = qid then sort_term else Base (new_qid, srts, a)
          | _ -> sort_term

      def translatePattern pat = pat

      def translateOpMap old_ops =
        let def translateStep (ref_qualifier, 
			       ref_id, 
			       (old_aliases as (primary_name as Qualified (primary_qualifier, primary_id))::_, 
				fixity, 
				sort_scheme, 
				optional_def),
			       new_opmap)
	    =
	    if ~ (ref_qualifier = primary_qualifier & ref_id = primary_id) then
	      (return new_opmap)
	    else
              let new_aliases = rev (foldl (fn (old_alias, new_aliases) -> 
					    let new_alias = translateQualifiedId (op_id_map, old_alias) in
					    if  member (new_alias, new_aliases) then
					      new_aliases
					    else 
					      Cons(new_alias, new_aliases))
				           [] 
					   old_aliases)
	      in
	      { first_opinfo  <- return (new_aliases, fixity, sort_scheme, optional_def);
	        merged_opinfo <- foldM (fn merged_opinfo -> fn (new_alias as Qualified (new_qualifier, new_id)) ->
					  mergeOpInfo merged_opinfo 
					              (findAQualifierMap (new_opmap, new_qualifier, new_id))
						      new_qualifier 
						      new_id position)
		                       first_opinfo
				       new_aliases;
	        foldM (fn new_opmap -> fn (Qualified (new_qualifier, new_id)) ->
		       return (insertAQualifierMap (new_opmap, new_qualifier, new_id, merged_opinfo)))
		      new_opmap  
		      new_aliases }
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_ops 

      def translateSortMap old_sorts =
        let def translateStep (ref_qualifier, 
			       ref_id, 
			       (old_aliases as (primary_name as Qualified (primary_qualifier, primary_id))::_, 
				ty_vars, 
				optional_def), 
			       new_sortmap) = 
	    if ~ (ref_qualifier = primary_qualifier & ref_id = primary_id) then
	      (return new_sortmap)
	    else
              let new_aliases = rev (foldl (fn (old_alias, new_aliases) -> 
					    let new_alias = translateQualifiedId (sort_id_map, old_alias) in
					    if  member (new_alias, new_aliases) then
					      new_aliases
					    else 
					      Cons(new_alias, new_aliases))
				           [] 
					   old_aliases)
	      in
	      { first_sortinfo  <- return (new_aliases, ty_vars, optional_def);
	        merged_sortinfo <- foldM (fn merged_sortinfo -> fn (new_alias as Qualified (new_qualifier, new_id)) ->
					  mergeSortInfo merged_sortinfo 
					                (findAQualifierMap (new_sortmap, new_qualifier, new_id))
						        new_qualifier 
						        new_id position)
		                         first_sortinfo
				         new_aliases;
	        foldM (fn new_sortmap -> fn (Qualified (new_qualifier, new_id)) ->
		       return (insertAQualifierMap (new_sortmap, new_qualifier, new_id, merged_sortinfo)))
		      new_sortmap  
		      new_aliases }
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_sorts 

    in
    let {importInfo = _, sorts, ops, properties}
         = mapSpec (translateOp, translateSort, translatePattern) spc
     %%         importedSpecs    = mapImports translateSpec importedSpecs
    in {
      newSorts <- translateSortMap sorts;
      newOps   <- translateOpMap   ops;
      return {
	      importInfo = emptyImportInfo,        % Could change if we get smarter
	      sorts      = newSorts,
	      ops        = newOps,
	      properties = properties
	     }
       }
  }
\end{spec}
