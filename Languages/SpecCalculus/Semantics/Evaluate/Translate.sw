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
    let 

      def insert (translation_op_map, translation_sort_map) (translation_rule, rule_pos) =

	let 
          def add_type_rule translation_op_map translation_sort_map (dom_qid as Qualified (dom_q, dom_id)) dom_types cod_qid cod_aliases =
	    (case dom_types of
	       | ((Qualified (found_q, _))::_,_,_)::other_aliases  ->
	          (if other_aliases = [] or found_q = UnQualified then
		   %% dom_qid has a unique referent, either because it refers to 
		   %% exactly one type, or becauses it is unqualified and refers 
		   %% to an unqualified type (perhaps among others), in which 
		   %% case that unqualified type is (by language definition) 
		   %% the unique unique referent.  
		   %% (Note that a qualified dom_qid can't refer to an unqualified 
		   %% type, so we can suppress the test for unqualified dom_qid.)						     
		   case findAQualifierMap (translation_sort_map, dom_q, dom_id) of
		     | None -> 
		       return (translation_op_map, 
			       insertAQualifierMap (translation_sort_map, dom_q, dom_id, (cod_qid, cod_aliases)))
		     | _  -> 
		       raise (MorphError (rule_pos, 
					  "(1) Translate: multiple rules for source type "^
					  (explicitPrintQualifiedId dom_qid)))
		   else 
		     raise (MorphError (rule_pos, "(2) Translate: ambiguous source type " ^ (explicitPrintQualifiedId dom_qid))))
	       | _ -> 
		 raise (MorphError (rule_pos, "(3) Translate: unrecognized source type " ^ (explicitPrintQualifiedId dom_qid))))
	      
	  def add_op_rule translation_op_map translation_sort_map (dom_qid as Qualified(dom_q, dom_id)) dom_ops cod_qid cod_aliases =
	    case dom_ops of
	      | ((Qualified (found_q, _))::_,_,_,_)::rs  ->
	        (if rs = [] or found_q = UnQualified then
		   %% See note above for types.
		   case findAQualifierMap (translation_op_map, dom_q, dom_id) of
		     | None -> 
		       %% No rule yet for dom_qid...
		       return (insertAQualifierMap (translation_op_map, dom_q, dom_id, (cod_qid, cod_aliases)),
			       translation_sort_map)
		     | _ -> 
		       %% Already had a rule for dom_qid...
		       raise (MorphError (rule_pos, 
					  "(4) Translate: multiple rules for source op "^
					  (explicitPrintQualifiedId dom_qid)))
		 else 
		   raise (MorphError (rule_pos, "(5) Translate: ambiguous source op "^   (explicitPrintQualifiedId dom_qid))))
	      | _ -> 
		raise (MorphError (rule_pos, "(6) Translate: unrecognized source op "^(explicitPrintQualifiedId dom_qid)))
		  
	  def add_wildcard_rules translation_op_map translation_sort_map dom_q cod_q cod_aliases =
	    %% Special hack for aggregate renamings: X._ +-> Y._
	    %% Find all dom sorts/ops qualified by X, and requalify them with Y
	    (if basicQualifier? dom_q then
	       raise (MorphError (position, "(7) Illegal to translate from base : " ^ dom_q))
	     else if basicQualifier? cod_q then
	       raise (MorphError (position, "(8) Illegal to translate into base: " ^ cod_q))
	     else
	       let

		 def extend_sort_map (sort_q, sort_id, _ (* sort_info *), translation_sort_map) =
		   if sort_q = dom_q then
		     %% This is a candidate to be translated...
		     case findAQualifierMap (translation_sort_map, sort_q, sort_id) of
		       | None -> 
		         %% No rule yet for this candidate...
		         let new_cod_qid = mkQualifiedId (cod_q, sort_id) in
			 return (insertAQualifierMap (translation_sort_map, sort_q, sort_id, (new_cod_qid, [new_cod_qid])))
		       | _ -> 
			 raise (MorphError (rule_pos, "(9) translate: Multiple (wild) rules for source sort "^
					    (explicitPrintQualifiedId (mkQualifiedId (sort_q, sort_id)))))
		   else
		     return translation_sort_map

                 def extend_op_map (op_q, op_id, _ (* op_info *), translation_op_map) =
		   if op_q = dom_q then
		     %% This is a candidate to be translated...
		     case findAQualifierMap (translation_op_map, op_q, op_id) of
		       | None -> 
		         %% No rule yet for this candidate...
		         let new_cod_qid = mkQualifiedId (cod_q, op_id) in
			 {
			  new_cod_qid <- (if syntactic_qid? new_cod_qid then
					    raise (MorphError (rule_pos,
							       "(10) `" ^ (explicitPrintQualifiedId new_cod_qid) ^ 
							       "' is syntax, not an op, hence cannot be the target of a translation. (B)"))
					  else
					    foldM (fn cod_qid -> fn alias ->
						   if syntactic_qid? alias then 
						     raise (MorphError (rule_pos,
									"(11) Alias `" ^ (explicitPrintQualifiedId alias) ^ 
									"' is syntax, not an op, hence cannot be the target of a translation. (B)"))
						   else
						     return cod_qid)
					          new_cod_qid
						  cod_aliases);
			  return (insertAQualifierMap (translation_op_map, op_q, op_id, (new_cod_qid, [new_cod_qid])))
			 }
		       | _ -> 
			 %% Candidate already has a rule (e.g. via some explicit mapping)...
			 raise (MorphError (rule_pos, "(12) translate: Multiple (wild) rules for source op "^
					    (explicitPrintQualifiedId (mkQualifiedId (op_q, op_id)))))
		   else
		     return translation_op_map 
	       in 
		 {
		  %% Check each dom type and op to see if this abstract ambiguous rule applies...
		  translation_sort_map <- foldOverQualifierMap extend_sort_map translation_sort_map dom_spec.sorts;
		  translation_op_map   <- foldOverQualifierMap extend_op_map   translation_op_map   dom_spec.ops;
		  return (translation_op_map, translation_sort_map)
		 })

    in

      case translation_rule of
	
	%% TODO: ?? Add special hack for aggregate type renamings: X._ +-> Y._  ??
	%% TODO: ?? Add special hack for aggregate op   renamings: X._ +-> Y._  ??

        | Sort (dom_qid, cod_qid, cod_aliases) -> 
	  if basicQualifiedId? dom_qid then
	    raise (MorphError (position, "(13) Illegal to translate from base type : " ^ (explicitPrintQualifiedId dom_qid)))
	  else if basicQualifiedId? cod_qid then
	    raise (MorphError (position, "(14) Illegal to translate into base type: " ^ (explicitPrintQualifiedId cod_qid)))
	  else
	    let dom_types = findAllSorts (dom_spec, dom_qid) in
	    add_type_rule translation_op_map translation_sort_map dom_qid dom_types cod_qid cod_aliases

	| Op   ((dom_qid, dom_type), (cod_qid, cod_type), cod_aliases) ->  
	  if syntactic_qid? dom_qid then 
	    raise (MorphError (rule_pos,
			       "(15) `" ^ (explicitPrintQualifiedId dom_qid) ^ "' is syntax, not an op, hence cannot be translated. (C)"))
	  else if basicQualifiedId? dom_qid then
	    raise (MorphError (position, "(16) Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid)))
	  else if basicQualifiedId? cod_qid then
	    raise (MorphError (position, "(17) Illegal to translate into base op: " ^ (explicitPrintQualifiedId cod_qid)))
	  else
	    let dom_ops = findAllOps (dom_spec, dom_qid) in
	    add_op_rule translation_op_map translation_sort_map dom_qid dom_ops cod_qid cod_aliases

	| Ambiguous (Qualified(dom_q, "_"), Qualified(cod_q,"_"), cod_aliases) -> 
	  add_wildcard_rules translation_op_map translation_sort_map dom_q cod_q cod_aliases

	| Ambiguous (dom_qid, cod_qid, cod_aliases) -> 
	  if syntactic_qid? dom_qid then 
	    raise (MorphError (rule_pos, "(18) `" ^ (explicitPrintQualifiedId dom_qid) ^ "' is syntax, not an op, hence cannot be translated. (D)"))
	  else if basicQualifiedId? dom_qid then
	    raise (MorphError (position, "(19) Illegal to translate from base type or op: " ^ (explicitPrintQualifiedId dom_qid)))
	  else if basicQualifiedId? cod_qid then
	    raise (MorphError (position, "(20) Illegal to translate into base type or op: " ^ (explicitPrintQualifiedId cod_qid)))
	  else
	    %% Find a sort or an op, and proceed as above
	    let dom_types = findAllSorts (dom_spec, dom_qid) in
	    let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	    case (dom_types, dom_ops) of
	      | ([], []) -> raise (MorphError (rule_pos, "(21) translate: Unrecognized source type or op "^(explicitPrintQualifiedId dom_qid)))
	      | (_,  []) -> add_type_rule translation_op_map translation_sort_map dom_qid dom_types cod_qid cod_aliases
	      | ([], _)  -> add_op_rule   translation_op_map translation_sort_map dom_qid dom_ops   cod_qid cod_aliases
	      | (_,  _)  -> raise (MorphError (rule_pos, "(22) translate: Ambiguous source type or op: "^(explicitPrintQualifiedId dom_qid)))
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
		| "~"    -> fail ("Problem in translateOp")
		| "&"    -> fail ("Problem in translateOp")
		| "&&"   -> fail ("Problem in translateOp")
		| "or"   -> fail ("Problem in translateOp")
		| "||"   -> fail ("Problem in translateOp")
		| "=>"   -> fail ("Problem in translateOp")
		| "<=>"  -> fail ("Problem in translateOp")
		| "="    -> fail ("Problem in translateOp")
		| "~="   -> fail ("Problem in translateOp")
		| _ -> 
		  if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a))
	   | Qualified ("<unqualified>", x) ->
	     (case x of
		| "~"    -> fail ("Problem in translateOp")
		| "&"    -> fail ("Problem in translateOp")
		| "&&"   -> fail ("Problem in translateOp")
		| "or"   -> fail ("Problem in translateOp")
		| "||"   -> fail ("Problem in translateOp")
		| "=>"   -> fail ("Problem in translateOp")
		| "<=>"  -> fail ("Problem in translateOp")
		| "="    -> fail ("Problem in translateOp")
		| "~="   -> fail ("Problem in translateOp")
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
    %% TODO: ?? Change UnQualified to new_q in all qualified names ??
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
        let def translateStep (ref_q, 
			       ref_id, 
			       old_opinfo as
			       (old_aliases as (primary_name as Qualified (primary_q, primary_id))::_, 
				fixity, 
				sort_scheme, 
				defs),
			       new_op_map)
	    =
	    if ~ (ref_q = primary_q & ref_id = primary_id) then
	      return new_op_map
	    else if basicQualifier? ref_q then
	      return (insertAQualifierMap (new_op_map, ref_q, ref_id, old_opinfo))
	    else
	      {
	       new_aliases <- foldM (fn new_aliases -> fn old_alias ->
				     foldM (fn new_aliases -> fn new_alias ->
					    if member (new_alias, new_aliases) then
					      return new_aliases
					    else 
					      return (Cons(new_alias, new_aliases)))
				           new_aliases
					   (translateOpQualifiedIdToAliases op_id_map old_alias))
	                            [] 
				    old_aliases;
	       new_aliases <- return (rev new_aliases);
	       mapM (fn old_alias ->
		     if basicQualifiedId? old_alias then
		       raise (MorphError (position, "(23) Illegal to translate base op " ^ (explicitPrintQualifiedId old_alias)))
		     else
		       return old_alias)
	            old_aliases;
	       first_opinfo  <- return (new_aliases, fixity, sort_scheme, defs);
	       merged_opinfo <- foldM (fn merged_opinfo -> fn (new_alias as Qualified (new_q, new_id)) ->
					  mergeOpInfo spc
					              merged_opinfo 
					              (findAQualifierMap (new_op_map, new_q, new_id))
						      position)
		                       first_opinfo
				       new_aliases;
	       foldM (fn new_op_map -> fn (Qualified (new_q, new_id)) ->
		      return (insertAQualifierMap (new_op_map, new_q, new_id, merged_opinfo)))
	             new_op_map  
		     new_aliases 
	      }
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_ops 

      def translateSortMap old_sorts =
        let def translateStep (ref_q, 
			       ref_id, 
			       old_sortinfo as
			       (old_aliases as (primary_name as Qualified (primary_q, primary_id))::_, 
				ty_vars, 
				defs),
			       new_sort_map) = 
	    if ~ (ref_q = primary_q & ref_id = primary_id) then
	      return new_sort_map
	    else if basicQualifier? ref_q then
	      return (insertAQualifierMap (new_sort_map, ref_q, ref_id, old_sortinfo))
	    else
	      {
	       new_aliases <- foldM (fn new_aliases -> fn old_alias ->
				     foldM (fn new_aliases -> fn new_alias ->
					    if member (new_alias, new_aliases) then
					      return new_aliases
					    else 
					      return (Cons(new_alias, new_aliases)))
				           new_aliases
					   (translateSortQualifiedIdToAliases sort_id_map old_alias))
	                            [] 
				    old_aliases;
	       new_aliases <- return (rev new_aliases);
	       mapM (fn old_alias ->
		     if basicQualifiedId? old_alias & ~ (member (old_alias, new_aliases)) then
		       raise (MorphError (position, "(24) Illegal to translate base type " ^ (explicitPrintQualifiedId old_alias)))
		     else
		       return old_alias)
	            old_aliases;
	       if member (unqualified_Boolean,  new_aliases) or member (Boolean_Boolean,  new_aliases) then
		 return new_sort_map
	       else
		{ first_sortinfo  <- return (new_aliases, ty_vars, defs);
		  merged_sortinfo <- foldM (fn merged_sortinfo -> fn (new_alias as Qualified (new_q, new_id)) ->
					    mergeSortInfo spc
					                  merged_sortinfo 
							  (findAQualifierMap (new_sort_map, new_q, new_id))
							  position)
		                           first_sortinfo
					   new_aliases;
		  foldM (fn new_sort_map -> fn (Qualified (new_q, new_id)) ->
			 return (insertAQualifierMap (new_sort_map, new_q, new_id, merged_sortinfo)))
		        new_sort_map  
			new_aliases 
		       }}
		
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
