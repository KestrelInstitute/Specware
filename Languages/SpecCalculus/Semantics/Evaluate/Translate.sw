\subsection{Spec Translation}

TODO: This has file suffers greatly from having to accommodate the representation
of specs, ops, sorts and ids. 

Also the parser seems to set up a cod_aliases field. I would argue that
this should be removed from the parser. I disagree. I, on the other hand,
agree with myself. I couldn't agree more.

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import Spec/Utilities
  import UnitId/Utilities                                % for uidToString, if used...
\end{spec}

Perhaps evaluating a translation should yield a morphism rather than just 
a spec. Then perhaps we add dom and cod domain operations on morphisms.
Perhaps the calculus is getting too complicated.

\begin{spec}
  def SpecCalc.evaluateTranslate term translation = {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-translation at " ^ (uidToString unitId)^"\n");
    (value,timeStamp,depUIDs) <- evaluateTermInfo term;
    case coerceToSpec value of
      | Spec spc -> {
            spcTrans <- translateSpec spc translation;
            return (Spec spcTrans,timeStamp,depUIDs)
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
    %% Similar to code in SpecMorphism.sw
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
				      %% We allow Qualified("Boolean", "Boolean") as a cod_qid,
				      %% but rely on translateSort to notice it and replace any 
				      %% resulting sort term with built-in Boolean.
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
		    | None -> 
		      {
		       cod_qid <- (if syntactic_qid? cod_qid then 
				     raise (MorphError (rule_pos,
							"`" ^ (printQualifiedId cod_qid) ^ "' is syntax, not an op, hence cannot be the target of a translation."))
				   else
				     foldM (fn cod_qid -> fn alias ->
					    if syntactic_qid? alias then 
					      raise (MorphError (rule_pos,
								 "Alias `" ^ (printQualifiedId alias) ^ "' is syntax, not an op, hence cannot be the target of a translation."))
					    else
					      return cod_qid)
				            cod_qid
					    cod_aliases);
		       return (insertAQualifierMap (translation_op_map, dom_qualifier, dom_id, (cod_qid, cod_aliases)),
			       translation_sort_map)
		      }
		    | _ -> raise (SpecError (rule_pos, 
						"translate: Duplicate rules for source op "^
						(printQualifiedId dom_qid)))
		else 
		  raise (SpecError (rule_pos, "translate: Ambiguous source op "^   (printQualifiedId dom_qid)))) 
	     | _ -> 
		  raise (SpecError (rule_pos, "translate: Unrecognized source op "^(printQualifiedId dom_qid))))

    	| Ambiguous (Qualified(dom_qualifier, "_"), Qualified(cod_qualifier,"_"), cod_aliases) -> 
            let
              def extend_op_map (op_qualifier, op_id, _ (* op_info *), translation_op_map) =
                if op_qualifier = dom_qualifier then
                  case findAQualifierMap (translation_op_map, op_qualifier,op_id) of
                    | None -> 
		      let new_cod_qid = mkQualifiedId (cod_qualifier, op_id) in
		      {
		       new_cod_qid <- (if syntactic_qid? new_cod_qid then
					 raise (MorphError (rule_pos,
							    "`" ^ (printQualifiedId new_cod_qid) ^ "' is syntax, not an op, hence cannot be the target of a translation."))
				       else
					 foldM (fn cod_qid -> fn alias ->
						if syntactic_qid? alias then 
						  raise (MorphError (rule_pos,
								     "Alias `" ^ (printQualifiedId alias) ^ "' is syntax, not an op, hence cannot be the target of a translation."))
						else
						  return cod_qid)
					       new_cod_qid
					       cod_aliases);
		       return (insertAQualifierMap (translation_op_map, op_qualifier, op_id, (new_cod_qid, [new_cod_qid])))
		       }
                    | _ -> raise (SpecError (rule_pos, "translate: Duplicate rules for source op "^
                                                       (printQualifiedId (mkQualifiedId (op_qualifier,op_id)))))
                else
                  return translation_op_map 
              def extend_sort_map (sort_qualifier, sort_id, _ (* sort_info *), translation_sort_map) =
                if sort_qualifier = dom_qualifier then
                  case findAQualifierMap (translation_sort_map, sort_qualifier, sort_id) of
                    | None -> 
                        let new_cod_qid = case (cod_qualifier, sort_id) of
					    %% We allow Qualified("Boolean", "Boolean") as a cod_qid,
					    %% but rely on translateSort to notice it and replace any 
					    %% resulting sort term with built-in Boolean.
		                            | ("<unqualified>", "Boolean") -> Boolean_Boolean
					    | _ -> mkQualifiedId (cod_qualifier, sort_id)
                        in
                        return (insertAQualifierMap (translation_sort_map, sort_qualifier, sort_id, (new_cod_qid, [new_cod_qid])))
                    | _ -> raise (SpecError (rule_pos, "translate: Duplicate rules for source sort "^
    						       (printQualifiedId (mkQualifiedId (sort_qualifier,sort_id)))))
                else
                  return translation_sort_map
            in {
              translation_op_map   <- foldOverQualifierMap extend_op_map   translation_op_map   dom_spec.ops;
              translation_sort_map <- foldOverQualifierMap extend_sort_map translation_sort_map dom_spec.sorts;
              return (translation_op_map, translation_sort_map)
            }
	| Ambiguous (dom_qid as Qualified(dom_qualifier, dom_id), cod_qid, cod_aliases) -> 
          (let dom_sorts = findAllSorts (dom_spec, dom_qid) in
	   let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	   case (dom_sorts, dom_ops) of

             %% neither:
	     | ([], []) ->
	       raise (SpecError (rule_pos, "translate: Unrecognized source sort/op "^(printQualifiedId dom_qid)))

	     %% Sort(s) only:
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

	     %% Op(s) only:
	     | ([], ((Qualified (found_qualifier, _))::_,_,_,_)::rs) ->
	       if rs = [] or found_qualifier = UnQualified then
		 case findAQualifierMap (translation_op_map, dom_qualifier, dom_id) of
		   | None -> 
		     { 
		      cod_qid <- (if syntactic_qid? cod_qid then
				    raise (MorphError (rule_pos,
						       "`" ^ (printQualifiedId cod_qid) ^ "' is syntax, not an op, hence cannot be the target of a translation."))
				  else
				    foldM (fn cod_qid -> fn alias ->
					   if syntactic_qid? alias then 
					     raise (MorphError (rule_pos,
								"Alias `" ^ (printQualifiedId alias) ^ "' is syntax, not an op, hence cannot be the target of a translation."))
					   else
					     return cod_qid)
				          cod_qid
					  cod_aliases);
		      return (insertAQualifierMap (translation_op_map, dom_qualifier, dom_id, (cod_qid, cod_aliases)),
			      translation_sort_map)
		     }
		   | _ -> raise (SpecError (rule_pos, 
						"translate: Duplicate rules for source op "^
						(printQualifiedId dom_qid)))
	       else
		 raise (SpecError (rule_pos, "translate: Ambiguous source op "^(printQualifiedId dom_qid))) % should be same as dom_id

             %% Both sort(s) and op(s):
	     | (_, _) ->
	       raise (SpecError (rule_pos, "translate: Ambiguous source is both sort and op " ^ (printQualifiedId dom_qid))))
    in
      foldM insert (emptyAQualifierMap, emptyAQualifierMap) translation_rules

  op  translateOpQualifiedId:   AQualifierMap(QualifiedId * Aliases) -> QualifiedId -> QualifiedId
  op  translateSortQualifiedId: AQualifierMap(QualifiedId * Aliases) -> QualifiedId -> QualifiedId
  op  translateOp:   AQualifierMap(QualifiedId * Aliases) -> MS.Term -> MS.Term
  op  translateSort: AQualifierMap(QualifiedId * Aliases) -> MS.Sort -> MS.Sort

  def translateOpQualifiedId op_id_map (qid as Qualified (qualifier, id)) =
    case findAQualifierMap (op_id_map, qualifier,id) of
      | Some (nQId,_) -> nQId
      | None -> qid

  def translateSortQualifiedId sort_id_map (qid as Qualified (qualifier, id)) =
    case findAQualifierMap (sort_id_map, qualifier,id) of
      | Some (nQId,_) -> nQId
      | None -> qid

  def translateOp op_id_map op_term =
    case op_term of
      | Fun (Op (qid, fixity), srt, a) ->
	(let new_qid = translateOpQualifiedId op_id_map qid in
	 case new_qid of
	   | Qualified ("Boolean", x) ->
	     (case x of
		| "~"    -> Fun (Not       , srt, a)
		| "&"    -> Fun (And       , srt, a)
		| "or"   -> Fun (Or        , srt, a)
		| "=>"   -> Fun (Implies   , srt, a)
		| "<=>"  -> Fun (Iff       , srt, a)
		| "="    -> Fun (Equals    , srt, a)
		| "~="   -> Fun (NotEquals , srt, a)
		| _ -> 
		  if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a))
	   | Qualified ("<unqualified>", x) ->
	     (case x of
		| "~"    -> Fun (Not       , srt, a)
		| "&"    -> Fun (And       , srt, a)
		| "or"   -> Fun (Or        , srt, a)
		| "=>"   -> Fun (Implies   , srt, a)
		| "<=>"  -> Fun (Iff       , srt, a)
		| "="    -> Fun (Equals    , srt, a)
		| "~="   -> Fun (NotEquals , srt, a)
		| _ -> 
		  if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a))
	   | _ ->
		if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a))
      | _ -> op_term

  def translateSort sort_id_map sort_term =
    case sort_term of
      | Base (qid, srts, a) ->
	(let new_qid = translateSortQualifiedId sort_id_map qid in
	 if new_qid = Boolean_Boolean then
	   Boolean a
	 else if new_qid = unqualified_Boolean then
	   Boolean a
	 else if new_qid = qid then 
	   sort_term 
	 else 
	   Base (new_qid, srts, a))
      | _ -> sort_term


  op auxTranslateSpec :
        Spec
     -> AQualifierMap (QualifiedId * Aliases) * AQualifierMap (QualifiedId * Aliases)
     -> Position
     -> SpecCalc.Env Spec

  def auxTranslateSpec spc (op_id_map, sort_id_map) position =
    %% TODO: need to avoid capture that occurs for "X +-> Y" in "fa (Y) ...X..."
    %% TODO: ?? Change UnQualified to new_qualifier in all qualified names ??
    let
      def translateOpQualifiedIdToAliases op_id_map (qid as Qualified (qualifier, id)) =
        case findAQualifierMap (op_id_map, qualifier,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translateSortQualifiedIdToAliases sort_id_map (qid as Qualified (qualifier, id)) =
        case findAQualifierMap (sort_id_map, qualifier,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
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
					          (translateOpQualifiedIdToAliases op_id_map old_alias))
				           [] 
					   old_aliases)
	      in
	      { first_opinfo  <- return (new_aliases, fixity, sort_scheme, defs);
	        merged_opinfo <- foldM (fn merged_opinfo -> fn (new_alias as Qualified (new_qualifier, new_id)) ->
					  mergeOpInfo spc
					              merged_opinfo 
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
					          (translateSortQualifiedIdToAliases sort_id_map old_alias))
				           [] 
					   old_aliases)
	      in
	      if new_aliases = [Qualified(UnQualified,"Boolean")] then
		return new_sort_map
	      else
		{ first_sortinfo  <- return (new_aliases, ty_vars, defs);
		  merged_sortinfo <- foldM (fn merged_sortinfo -> fn (new_alias as Qualified (new_qualifier, new_id)) ->
					    mergeSortInfo spc
					                  merged_sortinfo 
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
         = mapSpec (translateOp op_id_map, translateSort sort_id_map, translatePattern) spc
    in {
      newSorts <- translateSortMap sorts;
      newOps   <- translateOpMap   ops;
      return {
	      importInfo = {
			    imports      = [],
			    importedSpec = None,
			    localOps     = map (translateOpQualifiedId op_id_map) localOps,
			    localSorts   = foldl (fn (ty, local_types) -> 
						  let new_type = translateSortQualifiedId sort_id_map ty in
						  %% Avoid adding Boolean or Boolean.Boolean to local sorts,
						  %% since it is built in.
						  if new_type = Boolean_Boolean or new_type = unqualified_Boolean then
						    local_types
						  else
						    local_types ++ [new_type])
			                         []
						 localSorts
			   },  
	      sorts      = newSorts,
	      ops        = newOps,
	      properties = properties
	     }
       }
  }
\end{spec}
