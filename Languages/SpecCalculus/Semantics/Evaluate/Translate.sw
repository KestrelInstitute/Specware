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
  def SpecCalc.evaluateTranslate term translation = {
      (value,timeStamp,depURIs) <- evaluateTermInfo term;
      case coerceToSpec value of
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

If the following, assume we are given the rule "<lhs> +-> <rhs>"

We lookup <lhs> in the domain spec to find a domain item, raising an exception
if nothing can be found.  The rules are intended to be the same as those used
when linking names in formulas within a spec, but the keywords "sort" and "op" 
are allowed here to disambiguate an otherwise missing context:

\begin{verbatim}
  "sort [A.]X"   will look at sorts only
  "op   [A.]X"   will look at ops   only
  "[A.]X"        will look at sorts and ops, raising an exception if there are both
  "[A.]f : B.X"  will lookup [A.]f of type [B.]X
  "X"            will find unqualified "X" in preference to "A.X" if both exist.
\end{verbatim}

Translate all references to the found item into <rhs>, withe following
caveats:

\begin{itemize}
\item If <rhs> lacks an explicit qualifier, the rhs item is unqualified.

\item If multiple lhs items map to the same rhs item, then their (translated)
      properties (e.g. types or definitions) must be mergable or an exception 
      is raised.

\item Given sorts A and B, plus ops (f : A) and (f : B), if A and B are both
      mapped to the same C, then (f : A) and (f : B) will implicitly map to 
      the same rhs item (unless they are explicitly mapped elsewhere).

\end{itemize}

Note: The code below does not yet match the documentation above, but should.

\begin{spec}
  op translateSpec : Spec -> TranslateExpr Position -> Env Spec
  def translateSpec spc expr = {
      translation_maps <- makeTranslationMaps spc expr;
      new_spec <- auxTranslateSpec spc translation_maps (positionOf expr);
      complainIfAmbiguous (compressDefs new_spec) (positionOf expr)
    } 
    
  op makeTranslationMaps :
        Spec
     -> TranslateExpr Position
     -> SpecCalc.Env (AQualifierMap (QualifiedId * Aliases) * AQualifierMap (QualifiedId * Aliases))
  def makeTranslationMaps dom_spec (translation_rules, position) =
    %% Similar to code in SpecMorphism.sw, but this is monadic, 
    %% and types are factored as Foo a = (Foo_ a) * a
    %% TODO:  Detect multiple rules for same dom item.
    let def insert (translation_op_map, translation_sort_map) (translation_rule, rule_pos) =
      case translation_rule of

	| Sort (dom_qid as Qualified (dom_qualifier, dom_id), cod_qid, cod_aliases) -> 
	  (case findAllSorts (dom_spec, dom_qid) of
	     | ((Qualified (found_qualifier, _))::_,_,_)::rs  ->
	       (if rs = [] or found_qualifier = UnQualified then
                  case findAQualifierMap (translation_sort_map, dom_qualifier, dom_id) of
		    | None -> return (translation_op_map, 
				      insertAQualifierMap (translation_sort_map, dom_qualifier, dom_id, (cod_qid, cod_aliases)))
		    | _    -> raise (SpecError (rule_pos, 
						"translate: Duplicate rules for source sort "^
						(printQualifiedId dom_qid)))
		else 
		  raise (SpecError (rule_pos, "translate: Ambiguous source sort "^   (printQualifiedId dom_qid)))) 
	     | _ -> 
		  raise (SpecError (rule_pos, "translate: Unrecognized source sort "^(printQualifiedId dom_qid))))

	| Op ((dom_qid as Qualified(dom_qualifier, dom_id), dom_sort), (cod_qid, cod_sort), cod_aliases) -> 
	  %% TODO:  Currently ignores sort information.
	  (case findAllOps (dom_spec, dom_qid) of
	     | ((Qualified (found_qualifier, _))::_,_,_,_)::rs  ->
	       (if rs = [] or found_qualifier = UnQualified then
                  case findAQualifierMap (translation_op_map, dom_qualifier, dom_id) of
		    | None -> return (insertAQualifierMap (translation_op_map, dom_qualifier, dom_id, (cod_qid, cod_aliases)),
				      translation_sort_map)
		    | _ -> raise (SpecError (rule_pos, 
						"translate: Duplicate rules for source op "^
						(printQualifiedId dom_qid)))
		else 
		  raise (SpecError (rule_pos, "translate: Ambiguous source op "^   (printQualifiedId dom_qid)))) 
	     | _ -> 
		  raise (SpecError (rule_pos, "translate: Unrecognized source op "^(printQualifiedId dom_qid))))

	| Ambiguous (dom_qid as Qualified(dom_qualifier, dom_id), cod_qid, cod_aliases) -> 
          (let dom_sorts = findAllSorts (dom_spec, dom_qid) in
	   let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	   case (dom_sorts, dom_ops) of
	     | ([], []) ->
	       raise (SpecError (rule_pos, "translate: Unrecognized source sort/op "^(printQualifiedId dom_qid)))

	     | (((Qualified (found_qualifier, _))::_,_,_)::rs, [])  ->
	       if rs = [] or found_qualifier = UnQualified then
		 case findAQualifierMap (translation_sort_map, dom_qualifier, dom_id) of
		   | None -> return (translation_op_map, 
				     insertAQualifierMap (translation_sort_map, dom_qualifier, dom_id, (cod_qid, cod_aliases)))
		   | _ -> raise (SpecError (rule_pos, 
						"translate: Duplicate rules for source sort "^
						(printQualifiedId dom_qid)))
	       else 
		 raise (SpecError (rule_pos, "translate: Ambiguous source sort "^(printQualifiedId dom_qid))) % should be same as dom_id

	     | ([], ((Qualified (found_qualifier, _))::_,_,_,_)::rs) ->
	       if rs = [] or found_qualifier = UnQualified then
		 case findAQualifierMap (translation_op_map, dom_qualifier, dom_id) of
		   | None -> return (insertAQualifierMap (translation_op_map, dom_qualifier, dom_id, (cod_qid, cod_aliases)),
				     translation_sort_map)
		   | _ -> raise (SpecError (rule_pos, 
						"translate: Duplicate rules for source op "^
						(printQualifiedId dom_qid)))
	       else
		 raise (SpecError (rule_pos, "translate: Ambiguous source op "^(printQualifiedId dom_qid))) % should be same as dom_id

	     | (_, _) ->
	       raise (SpecError (rule_pos, "translate: Ambiguous source sort/op "^(printQualifiedId dom_qid))))
    in
      foldM insert (emptyAQualifierMap, emptyAQualifierMap) translation_rules

  op auxTranslateSpec :
        Spec
     -> AQualifierMap (QualifiedId * Aliases) * AQualifierMap (QualifiedId * Aliases)
     -> Position
     -> SpecCalc.Env Spec

  def auxTranslateSpec spc (op_id_map, sort_id_map) position =
    %% TODO: need to avoid capture that occurs for "X +-> Y" in "fa (Y) ...X..."
    %% TODO: ?? Change UnQualified to new_qualifier in all qualified names ??
    let
      def translateOpQualifiedId (qid as Qualified (qualifier, id)) =
        case findAQualifierMap (op_id_map, qualifier,id) of
          | Some (nQId,_) -> nQId
          | None -> qid
  
      def translateSortQualifiedId (qid as Qualified (qualifier, id)) =
        case findAQualifierMap (sort_id_map, qualifier,id) of
          | Some (nQId,_) -> nQId
          | None -> qid
  
      def translateOpQualifiedIdToAliases (qid as Qualified (qualifier, id)) =
        case findAQualifierMap (op_id_map, qualifier,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translateSortQualifiedIdToAliases (qid as Qualified (qualifier, id)) =
        case findAQualifierMap (sort_id_map, qualifier,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translateOp op_term =
        case op_term of
          | Fun (Op (qid, fixity), srt, a) ->
            let new_qid = translateOpQualifiedId qid in
            if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
          | _ -> op_term

      def translateSort sort_term =
        case sort_term of
          | Base (qid, srts, a) ->
             let new_qid = translateSortQualifiedId qid in
             if new_qid = qid then sort_term else Base (new_qid, srts, a)
          | _ -> sort_term

      def translatePattern pat = pat

      def translateOpMap old_ops =
        let def translateStep (ref_qualifier, 
			       ref_id, 
			       (old_aliases as (primary_name as Qualified (primary_qualifier, primary_id))::_, 
				fixity, 
				sort_scheme, 
				defs),
			       new_op_map)
	    =
	    if ~ (ref_qualifier = primary_qualifier & ref_id = primary_id) then
	      (return new_op_map)
	    else
              let new_aliases = rev (foldl (fn (old_alias, new_aliases) -> 
					    foldl (fn (new_alias, new_aliases) ->
						   if  member (new_alias, new_aliases) then
						     new_aliases
						   else 
						     Cons(new_alias, new_aliases))
					          new_aliases
					          (translateOpQualifiedIdToAliases old_alias))
				           [] 
					   old_aliases)
	      in
	      { first_opinfo  <- return (new_aliases, fixity, sort_scheme, defs);
	        merged_opinfo <- foldM (fn merged_opinfo -> fn (new_alias as Qualified (new_qualifier, new_id)) ->
					  mergeOpInfo merged_opinfo 
					              (findAQualifierMap (new_op_map, new_qualifier, new_id))
						      position)
		                       first_opinfo
				       new_aliases;
	        foldM (fn new_op_map -> fn (Qualified (new_qualifier, new_id)) ->
		       return (insertAQualifierMap (new_op_map, new_qualifier, new_id, merged_opinfo)))
		      new_op_map  
		      new_aliases }
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_ops 

      def translateSortMap old_sorts =
        let def translateStep (ref_qualifier, 
			       ref_id, 
			       (old_aliases as (primary_name as Qualified (primary_qualifier, primary_id))::_, 
				ty_vars, 
				defs),
			       new_sort_map) = 
	    if ~ (ref_qualifier = primary_qualifier & ref_id = primary_id) then
	      (return new_sort_map)
	    else
              let new_aliases = rev (foldl (fn (old_alias, new_aliases) -> 
					    foldl (fn (new_alias, new_aliases) ->
						   if  member (new_alias, new_aliases) then
						     new_aliases
						   else 
						     Cons(new_alias, new_aliases))
					          new_aliases
					          (translateSortQualifiedIdToAliases old_alias))
				           [] 
					   old_aliases)
	      in
	      { first_sortinfo  <- return (new_aliases, ty_vars, defs);
	        merged_sortinfo <- foldM (fn merged_sortinfo -> fn (new_alias as Qualified (new_qualifier, new_id)) ->
					  mergeSortInfo merged_sortinfo 
					                (findAQualifierMap (new_sort_map, new_qualifier, new_id))
						        position)
		                         first_sortinfo
				         new_aliases;
	        foldM (fn new_sort_map -> fn (Qualified (new_qualifier, new_id)) ->
		       return (insertAQualifierMap (new_sort_map, new_qualifier, new_id, merged_sortinfo)))
		      new_sort_map  
		      new_aliases }
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_sorts 

    in
    let {importInfo = {imports,importedSpec,localOps,localSorts}, sorts, ops, properties}
         = mapSpec (translateOp, translateSort, translatePattern) spc
    in {
      newSorts <- translateSortMap sorts;
      newOps   <- translateOpMap   ops;
      return {
	      importInfo = {
			    imports      = [],
			    importedSpec = None,
			    localOps     = map translateOpQualifiedId   localOps,
			    localSorts   = map translateSortQualifiedId localSorts
			   },  
	      sorts      = newSorts,
	      ops        = newOps,
	      properties = properties
	     }
       }
  }
\end{spec}
