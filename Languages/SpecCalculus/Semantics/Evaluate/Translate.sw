\subsection{Spec Translation}

TODO: This has file suffers greatly from having to accommodate the representation
of specs, ops, sorts and ids. 

Also the parser seems to set up a cod_aliases field. I would argue that
this should be removed from the parser. I disagree. I, on the other hand,
agree with myself. I couldn't agree more.

\begin{spec}
SpecCalc qualifying spec
  import Signature 
  import Spec/CompressSpec
  import Spec/AccessSpec
  import Spec/MergeSpecs
  import Spec/VarOpCapture
  import UnitId/Utilities                                % for uidToString, if used...

\end{spec}

Perhaps evaluating a translation should yield a morphism rather than just 
a spec. Then perhaps we add dom and cod domain operations on morphisms.
Perhaps the calculus is getting too complicated.

\begin{spec}
  def SpecCalc.evaluateTranslate term renaming_expr = {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-translation at " ^ (uidToString unitId)^"\n");
    (value,timeStamp,depUIDs) <- evaluateTermInfo term;
    case coerceToSpec value of
      | Spec spc -> {
            spcTrans <- translateSpec true spc renaming_expr;
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
when linking names in formulas within a spec, but the keywords "type" and "op" 
are allowed here to disambiguate an otherwise missing context:

\begin{verbatim}
  "type [A.]X"   will look at types only
  "op   [A.]X"   will look at ops   only
  "[A.]X"        will look at types and ops, raising an exception if there are both
  "[A.]f : B.X"  will lookup [A.]f of type [B.]X
  "X"            will find unqualified "X" in preference to "A.X" if both exist.
\end{verbatim}

Translate all references to the found item into <rhs>, with the following
caveats:

\begin{itemize}
\item If <rhs> lacks an explicit qualifier, the rhs item is unqualified.

\item Multiple lhs items may not map to the same rhs item.

\end{itemize}

Note: The code below does not yet match the documentation above, but should.

\begin{spec}

  %% translateSpec is used by Translate and Colimt
  %% When called from Colimit, require_monic? is false, and we should avoid
  %% raising exceptions...
  op  translateSpec : Boolean -> Spec -> RenamingExpr Position -> Env Spec
  def translateSpec require_monic? spc renaming_expr = 
    let pos = positionOf renaming_expr in
    {
     renamings <- makeRenamings require_monic? spc renaming_expr;
     raise_any_pending_exceptions;

     % reconstructed_expr <- reconstructRenamingExpr renamings;
     % print ("\n========\n");
     % print (showTerm (Translate ((Quote (Spec spc), noPos), expr), noPos));
     % print ("\n========\n");
     %%
     %% renamings is now an explicit map for which each name in its 
     %% domain refers to a particular type or op in the domain spec.  
     %%
     %% Each rule explicitly states that it is mapping a type or an op, 
     %% and there are no wildcards.   
     %%
     %% No two lhs items (types or ops) map to the same rhs item.
     %%
     %% makeRenamings will have raised various exceptions if it 
     %% cannot guarantee all of this
     %% 
     %% [Note that if an unqualified Y refers to B.Y in the domain spec,  
     %%  the typechecker will have resolved that reference from 
     %%  "<UnQualified>.Y" to "B.Y", so even if some X is translated to 
     %%  unqualified Y, the original refs via an unqualified Y will 
     %%  have been modified so that they translate along with B.Y to refer 
     %%  safely to B.Y]
     %%
     %% Now we produce a new spec using these unmbiguous maps.
     %% Note that auxTranslateSpec is not expected to raise any errors.
     
     spc <- auxTranslateSpec spc renamings (Some renaming_expr) pos;
     raise_any_pending_exceptions; % should never happen here
     
     %% Next we worry about traditional captures in which a (global) op Y,
     %% used under a binding of var X, is renamed to X.   Internally, this 
     %% is not a problem, since the new refs to op X are distinguishable 
     %% from the refs to var X, but printing the resulting formula loses
     %% that distinction, so refs to the op X that are under the binding 
     %% of var X would be read back in as refs to the var X.
     %% 
     %% So we do alpha conversions if a bound var has an op of the same
     %% name under its scope:
     
     spc <- return (removeVarOpCaptures spc);
     
     %% One final pass to see if we've managed to collapse necessarily 
     %% distinct types (e.g. A = X * Y and B = Z | p), or necessarily
     %% distinct ops (e.g. op i = 4 and op j = "oops") onto the same name.
     
     complainIfAmbiguous (compressDefs spc) pos
    } 

  op  makeRenamings : Boolean -> Spec -> RenamingExpr Position -> SpecCalc.Env Renamings
  def makeRenamings require_monic? dom_spec (renaming_rules, position) =
    %% translateSpec is used by Translate and Colimt
    %% When called from Colimit, require_monic? is false, and we should avoid
    %% raising exceptions...
    let sorts = dom_spec.sorts in
    let ops   = dom_spec.ops   in
    let 

      def complain_if_sort_collision (sorts, sort_renaming, this_dom_q, this_dom_id, this_new_qid, rule_pos) =
	let collisions =
	    foldriAQualifierMap (fn (other_dom_q, other_dom_id, other_target, collisions) ->
				 case other_target of
				   | (other_new_qid, _) ->
				     if other_new_qid = this_new_qid then
				       let other_dom_qid = Qualified (other_dom_q, other_dom_id) in
				       let Some this_info = findAQualifierMap (sorts, this_dom_q, this_dom_id) in
				       if member (other_dom_qid, this_info.names) then
					 %% ok to map aliases to same new name
					 collisions
				       else
					 %% not legal to map unrelated type names to the same new name
					 collisions ++ [other_dom_qid]
				     else
				       collisions)
	                        []
				sort_renaming
	in
	 case collisions of
	   | [] -> return ()
	   | _ ->
	     let conflicting_names = 
	         case collisions of
		   | [name] -> " and type " ^ (explicitPrintQualifiedId name)
		   | first::rest ->
		     " and types " ^ (explicitPrintQualifiedId first) ^
		     (foldl (fn (qid, str) -> str ^ ", " ^ explicitPrintQualifiedId qid)
		      ""
		      rest)
	     in
	       {
		raise_later (TranslationError ("Illegal to translate both type " ^  (explicitPrintQualifiedId (Qualified(this_dom_q,this_dom_id))) ^
					       conflicting_names ^ 
					       " into " ^ (explicitPrintQualifiedId this_new_qid),
					       rule_pos));
		return ()
	       }

      def complain_if_op_collision (ops, op_renaming, this_dom_q, this_dom_id, this_new_qid, rule_pos) =
	let collisions =
	    foldriAQualifierMap (fn (other_dom_q, other_dom_id, other_target, collisions) ->
				 case other_target of
				   | (other_new_qid, _) ->
				     if other_new_qid = this_new_qid then
				       let other_dom_qid = Qualified (other_dom_q, other_dom_id) in
				       let Some this_info = findAQualifierMap (ops, this_dom_q, this_dom_id) in
				       if member (other_dom_qid, this_info.names) then
					 %% ok to map aliases to same new name
					 collisions
				       else
					 %% not legal to map unrelated type names to the same new name
					 collisions ++ [other_dom_qid]
				     else
				       collisions)
	                        []
				op_renaming
	in
	 case collisions of
	   | [] -> return ()
	   | _ ->
	     let conflicting_names = 
	         case collisions of
		   | [name] -> " and op " ^ (explicitPrintQualifiedId name)
		   | first::rest ->
		     " and ops " ^ (explicitPrintQualifiedId first) ^
		     (foldl (fn (qid, str) -> str ^ ", " ^ explicitPrintQualifiedId qid)
		      ""
		      rest)
	     in
	       {
		raise_later (TranslationError ("Illegal to translate both op " ^  (explicitPrintQualifiedId (Qualified(this_dom_q,this_dom_id))) ^
					       conflicting_names ^ 
					       " into " ^ (explicitPrintQualifiedId this_new_qid),
					       rule_pos));
		return ()
	       }

      def complain_if_type_collisions_with_priors (sorts, sort_renaming) =
	foldOverQualifierMap (fn (dom_q, dom_id, (new_qid as Qualified(new_q,new_id),_), _) ->
			      %% we're proposing to translate dom_q.dom_id into new_q.new_id
			      case findAQualifierMap (sorts, new_q, new_id) of
				| None -> 
				  %% new_q.new_id does not refer to a pre-existing type, so we're ok
				  return ()
				| Some prior_info -> 
				  %% new_q.new_id refers to a pre-existing type
				  case findAQualifierMap (sort_renaming, new_q, new_id) of
				    | Some _ -> 
				      %% but we're renaming new_q.new_id out of the way, so we're ok
				      return ()
				    | None ->
				      %% new_q.new_id refers to a pre-existing type, and is not being renamed away
				      if member (Qualified(dom_q,dom_id), prior_info.names) then
					%% but it's an alias of dom_q.dom_id, so we're just collapsing aliases to the same name
					return () 
				      else
					%% new_q, new_id is a pre-existing, untranslated, non-alias type
					raise_later (TranslationError ("Illegal to translate type " ^ (explicitPrintQualifiedId (Qualified(dom_q,dom_id))) ^
								       " into pre-existing, non-alias, untranslated " ^ (explicitPrintQualifiedId new_qid),
								       position)))
	                     ()
			     sort_renaming


      def complain_if_op_collisions_with_priors (ops, op_renaming) =
	foldOverQualifierMap (fn (dom_q, dom_id, (new_qid as Qualified(new_q,new_id),_), _) ->
			      %% we're proposing to translate dom_q.dom_id into new_q.new_id
			      case findAQualifierMap (ops, new_q, new_id) of
				| None -> 
				  %% new_q.new_id does not refer to a pre-existing op, so we're ok
				  return ()
				| Some prior_info -> 
				  %% new_q.new_id refers to a pre-existing op
				  case findAQualifierMap (op_renaming, new_q, new_id) of
				    | Some _ -> 
				      %% but we're renaming new_q.new_id out of the way, so we're ok
				      return ()
				    | None ->
				      %% new_q, new_id refers to a pre-existing op, and is not being renamed away
				      if member (Qualified(dom_q,dom_id), prior_info.names) then
					%% but it's an alias of dom_q.dom_id, so we're just collapsing aliases to the same name
					return ()
				      else
					%% new_q,new_id refers to pre-existing, untranslated, non-alias op 
					raise_later (TranslationError ("Illegal to translate op " ^ (explicitPrintQualifiedId (Qualified(dom_q,dom_id))) ^
								       " into pre-existing, non-alias, untranslated " ^ (explicitPrintQualifiedId new_qid),
								       position)))
	                     ()
			     op_renaming


      def insert (op_renaming, sort_renaming) (renaming_rule, rule_pos) =

	let 
          def add_type_rule op_renaming sort_renaming (dom_qid as Qualified (dom_q, dom_id)) dom_types cod_qid cod_aliases =
	    case dom_types of
	      | first_info :: other_infos ->
	        (let primary_dom_qid as Qualified (primary_q, primary_id) = primarySortName first_info in
		 if other_infos = [] || primary_q = UnQualified then
		  %% dom_qid has a unique referent, either because it refers to 
		  %% exactly one type, or becauses it is unqualified and refers 
		  %% to an unqualified type (perhaps among others), in which 
		  %% case that unqualified type is (by language definition) 
		  %% the unique unique referent.  
		  %% (Note that a qualified dom_qid can't refer to an unqualified 
		  %% type, so we can suppress the test for unqualified dom_qid.)						     
		  if basicSortName? primary_dom_qid then
		    {
		     raise_later (TranslationError ("Illegal to translate from base type : " ^ (explicitPrintQualifiedId dom_qid),
						    rule_pos));
		     return (op_renaming, sort_renaming)
		    }
		  else
		    case findAQualifierMap (sort_renaming, dom_q, dom_id) of
		      | None -> 
		        {
			 when require_monic?
			   (complain_if_sort_collision (sorts, sort_renaming, dom_q, dom_id, cod_qid, rule_pos));
			 new_sort_renaming <- return (insertAQualifierMap (sort_renaming, dom_q, dom_id, (cod_qid, cod_aliases)));
			 new_sort_renaming <- return (if dom_q = UnQualified && primary_q ~= UnQualified && dom_id = primary_id then
						   %% in rule X +-> Y, X refers to A.X
						   %% so both X and A.X should translate to Y
						   insertAQualifierMap (new_sort_renaming, primary_q, primary_id, (cod_qid, cod_aliases))
						 else 
						   new_sort_renaming);
			 return (op_renaming, new_sort_renaming)
			 }
		      | _  -> 
			{
			 raise_later (TranslationError ("Multiple rules for source type " ^ (explicitPrintQualifiedId dom_qid),
							rule_pos));
			 return (op_renaming, sort_renaming)
			}
		else 
		  {
		   raise_later (TranslationError ("Ambiguous source type " ^ (explicitPrintQualifiedId dom_qid), 
						  rule_pos));
		   return (op_renaming, sort_renaming)
		  })
	      | _ -> 
		{
		 raise_later (TranslationError ("Unrecognized source type " ^ (explicitPrintQualifiedId dom_qid),
						rule_pos));
		 return (op_renaming, sort_renaming)
		}
		  
	      
	  def add_op_rule op_renaming sort_renaming (dom_qid as Qualified(dom_q, dom_id)) dom_ops cod_qid cod_aliases =
	    case dom_ops of
	      | first_op :: other_ops ->
	        (let primary_dom_qid as Qualified (primary_q, primary_id) = primaryOpName first_op in
		 if other_ops = [] || primary_q = UnQualified then
		   %% See note above for types.
		   if basicOpName? primary_dom_qid then
		     {
		      raise_later (TranslationError ("Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid),
						     rule_pos));
		      return (op_renaming, sort_renaming)
		     }
		   else
		     case findAQualifierMap (op_renaming, dom_q, dom_id) of
		       
		       | None -> 
		         %% No rule yet for dom_qid...
		         {
			  when require_monic?
			   (complain_if_op_collision (ops, op_renaming, dom_q, dom_id, cod_qid, rule_pos));
			  new_op_renaming <- return (insertAQualifierMap (op_renaming, dom_q, dom_id, (cod_qid, cod_aliases)));
			  new_op_renaming <- return (if dom_q = UnQualified && primary_q ~= UnQualified && dom_id = primary_id then
						  %% in rule X +-> Y, X refers to A.X
						  %% so both X and A.X should translate to Y
						  insertAQualifierMap (new_op_renaming, primary_q, primary_id, (cod_qid, cod_aliases))
						else 
						  new_op_renaming);
			  return (new_op_renaming, sort_renaming)
			  }
		       | _ -> 
			 %% Already had a rule for dom_qid...
			 {
			  raise_later (TranslationError ("Multiple rules for source op "^
							 (explicitPrintQualifiedId dom_qid),
							 rule_pos));
			  return (op_renaming, sort_renaming)
			 }
		 else 
		   {
		    raise_later (TranslationError ("Ambiguous source op " ^ (explicitPrintQualifiedId dom_qid),
						   rule_pos));
		    return (op_renaming, sort_renaming)
		    })
	      | _ -> 
		{
		 raise_later (TranslationError ("Unrecognized source op " ^ (explicitPrintQualifiedId dom_qid),
						rule_pos));
		 return (op_renaming, sort_renaming)
		 }
		  
	  def add_wildcard_rules op_renaming sort_renaming dom_q cod_q cod_aliases =
	    %% Special hack for aggregate renamings: X._ +-> Y._
	    %% Find all dom sorts/ops qualified by X, and requalify them with Y
	    (if basicQualifier? dom_q then
	       {
		raise_later (TranslationError ("Illegal to translate from base : " ^ dom_q, 
					       position));
		return (op_renaming, sort_renaming)
		}
	     else
	       let

		 def extend_sort_renaming (sort_q, sort_id, _ (* sort_info *), sort_renaming) =
		   if sort_q = dom_q then
		     %% This is a candidate to be translated...
		     case findAQualifierMap (sort_renaming, sort_q, sort_id) of
		       | None -> 
		         %% No rule yet for this candidate...
		         let new_cod_qid = mkQualifiedId (cod_q, sort_id) in
			 {
			  when require_monic? 
			   (complain_if_sort_collision (sorts, sort_renaming, sort_q, sort_id, new_cod_qid, rule_pos));
			  return (insertAQualifierMap (sort_renaming, sort_q, sort_id, (new_cod_qid, [new_cod_qid])))
			 }
		       | _ -> 
			 {
			  raise_later (TranslationError ("Multiple (wild) rules for source type "^
							 (explicitPrintQualifiedId (mkQualifiedId (sort_q, sort_id))),
							 rule_pos));
			  return sort_renaming
			  }
		   else
		     return sort_renaming

                 def extend_op_renaming (op_q, op_id, _ (* op_info *), op_renaming) =
		   if op_q = dom_q then
		     %% This is a candidate to be translated...
		     case findAQualifierMap (op_renaming, op_q, op_id) of
		       | None -> 
		         %% No rule yet for this candidate...
		         let new_cod_qid = mkQualifiedId (cod_q, op_id) in
			 {
			  new_cod_qid <- (if syntactic_qid? new_cod_qid then
					    {
					     raise_later (TranslationError ("`" ^ (explicitPrintQualifiedId new_cod_qid) ^ 
									    "' is syntax, not an op, hence cannot be the target of a translation.",
									    rule_pos));
					     return new_cod_qid
					     }
					  else
					    foldM (fn cod_qid -> fn alias ->
						   if syntactic_qid? alias then 
						     {
						      raise_later (TranslationError ("Alias `" ^ (explicitPrintQualifiedId alias) ^ 
										     "' is syntax, not an op, hence cannot be the target of a translation.",
										     rule_pos));
						      return cod_qid
						      }
						   else
						     return cod_qid)
					          new_cod_qid
						  cod_aliases);
			  when require_monic? 
			   (complain_if_op_collision (ops, op_renaming, op_q, op_id, new_cod_qid, rule_pos));
			  return (insertAQualifierMap (op_renaming, op_q, op_id, (new_cod_qid, [new_cod_qid])))
			 }
		       | _ -> 
			 %% Candidate already has a rule (e.g. via some explicit mapping)...
			 {
			  raise_later (TranslationError ("Multiple (wild) rules for source op "^
							 (explicitPrintQualifiedId (mkQualifiedId (op_q, op_id))),
							 rule_pos));
			  return op_renaming
			  }
						  
		   else
		     return op_renaming 
	       in 
		 {
		  %% Check each dom type and op to see if this abstract ambiguous rule applies...
		  sort_renaming <- foldOverQualifierMap extend_sort_renaming sort_renaming sorts;
		  op_renaming   <- foldOverQualifierMap extend_op_renaming   op_renaming   ops;
		  return (op_renaming, sort_renaming)
		 })

    in
      case renaming_rule of
	
	%% TODO: ?? Add special hack for aggregate type renamings: X._ +-> Y._  ??
	%% TODO: ?? Add special hack for aggregate op   renamings: X._ +-> Y._  ??

        | Sort (dom_qid, cod_qid, cod_aliases) -> 
	  if basicSortName? dom_qid then
	    {
	     raise_later (TranslationError ("Illegal to translate from base type : " ^ (explicitPrintQualifiedId dom_qid),
					    rule_pos));
	     return (op_renaming, sort_renaming)
	    }
	  else 
	    let dom_types = findAllSorts (dom_spec, dom_qid) in
	    add_type_rule op_renaming sort_renaming dom_qid dom_types cod_qid cod_aliases

	| Op   ((dom_qid, dom_type), (cod_qid, cod_type), cod_aliases) ->  
	  if syntactic_qid? dom_qid then 
	    {
	     raise_later (TranslationError ("`" ^ (explicitPrintQualifiedId dom_qid) ^ "' is syntax, not an op, hence cannot be translated.",
					    rule_pos));
	     return (op_renaming, sort_renaming)
	    }
	  else if basicOpName? dom_qid then
	    {
	     raise_later (TranslationError ("Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid),
					    rule_pos));
	     return (op_renaming, sort_renaming)
	    }
	  else 
	    let dom_ops = findAllOps (dom_spec, dom_qid) in
	    add_op_rule op_renaming sort_renaming dom_qid dom_ops cod_qid cod_aliases

	| Ambiguous (Qualified(dom_q, "_"), Qualified(cod_q,"_"), cod_aliases) -> 
	  add_wildcard_rules op_renaming sort_renaming dom_q cod_q cod_aliases

	| Ambiguous (dom_qid, cod_qid, cod_aliases) -> 
	  if syntactic_qid? dom_qid then 
	    {
	     raise_later (TranslationError ("`" ^ (explicitPrintQualifiedId dom_qid) ^ "' is syntax, not an op, hence cannot be translated.",
					    rule_pos));
	     return (op_renaming, sort_renaming)
	     }
	  else if basicQualifiedId? dom_qid then
	    {
	     raise_later (TranslationError ("Illegal to translate from base type or op: " ^ (explicitPrintQualifiedId dom_qid),
					    rule_pos));
	     return (op_renaming, sort_renaming)
	     }
	  else
	    %% Find a sort or an op, and proceed as above
	    let dom_types = findAllSorts (dom_spec, dom_qid) in
	    let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	    case (dom_types, dom_ops) of
	      | ([], []) -> {
			     raise_later (TranslationError ("Unrecognized source type or op "^(explicitPrintQualifiedId dom_qid), 
							    rule_pos));
			     return (op_renaming, sort_renaming)
			     }
	      | (_,  []) -> add_type_rule op_renaming sort_renaming dom_qid dom_types cod_qid cod_aliases
	      | ([], _)  -> add_op_rule   op_renaming sort_renaming dom_qid dom_ops   cod_qid cod_aliases
	      | (_,  _)  -> {
			     raise_later (TranslationError ("Ambiguous source type or op: "^(explicitPrintQualifiedId dom_qid),
							    rule_pos));
			     return (op_renaming, sort_renaming)
			     }
    in
      {
       (op_renaming, sort_renaming) <- foldM insert (emptyAQualifierMap, emptyAQualifierMap) renaming_rules;
       when require_monic?
        {complain_if_type_collisions_with_priors (sorts, sort_renaming);
	 complain_if_op_collisions_with_priors   (ops, op_renaming)};
       return {
	       op_renaming     = op_renaming, 
	       sort_renaming   = sort_renaming,
	       other_renamings = None
	      }
       }
       

  def basicCodSortName? qid =
    let base_spec = getBaseSpec () in
    case findAllSorts (base_spec, qid) of
      | [] -> false
      | _  -> true

  def basicCodOpName? qid =
    let base_spec = getBaseSpec () in
    case findAllOps (base_spec, qid) of
      | [] -> false
      | _  -> true

  def basicCodName? qid =
    let base_spec = getBaseSpec () in
    case findAllSorts (base_spec, qid) of
      | [] ->
        (case findAllOps (base_spec, qid) of
	   | [] -> false
	   | _  -> true)
      | _ -> true

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  translateOpQualifiedId   : Renaming -> QualifiedId -> QualifiedId
  op  translateSortQualifiedId : Renaming -> QualifiedId -> QualifiedId
  op  translateOp              : Renaming -> MS.Term -> MS.Term
  op  translateSort            : Renaming -> MS.Sort -> MS.Sort

  def translateOpQualifiedId op_renaming (qid as Qualified (q, id)) =
    case findAQualifierMap (op_renaming, q,id) of
      | Some (nQId,_) -> nQId
      | None -> qid

  def translateSortQualifiedId sort_renaming (qid as Qualified (q, id)) =
    case findAQualifierMap (sort_renaming, q,id) of
      | Some (nQId,_) -> nQId
      | None -> qid

  def translateOp op_renaming op_term =
    case op_term of
      | Fun (Op (qid, fixity), srt, pos) ->
	(let new_qid = translateOpQualifiedId op_renaming qid in
	 if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, pos))
      | _ -> op_term

  def translateSort sort_renaming sort_term =
    case sort_term of
      | Base (qid, srts, pos) ->
	(let new_qid = translateSortQualifiedId sort_renaming qid in
	 if new_qid = qid then sort_term else Base (new_qid, srts, pos))
      | _ -> sort_term


  %% auxTranslateSpec is used by Translate, Substitute, and (indirectly) Colimt
  %% It should avoid raising any errors.
  %% In particular, if an operation such as translate wishes to signal errors in 
  %% some situations, those errors should be raised while Renamings is being 
  %% created, not here.
  op  auxTranslateSpec : Spec -> Renamings -> Option (RenamingExpr Position) -> Position -> SpecCalc.Env Spec
  def auxTranslateSpec spc renamings opt_renaming_expr position =
    let   op_renaming = renamings.op_renaming in
    let sort_renaming = renamings.sort_renaming in
    %% TODO: need to avoid capture that occurs for "X +-> Y" in "fa (Y) ...X..."
    %% TODO: ?? Change UnQualified to new_q in all qualified names ??
    let
      def translateOpQualifiedIdToAliases op_renaming (qid as Qualified (q, id)) =
        case findAQualifierMap (op_renaming, q,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translateSortQualifiedIdToAliases sort_renaming (qid as Qualified (q, id)) =
        case findAQualifierMap (sort_renaming, q,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translatePattern pat = pat

      def translateOpMap old_ops =
        let 
          def translateStep (old_q, old_id, old_info, new_op_renaming) =
	    let primary_qid as Qualified (primary_q, primary_id) = primaryOpName old_info in
	    if ~ (old_q = primary_q && old_id = primary_id) then
	      % let _ = toScreen("\nIgnoring op info for " ^ old_q ^ "." ^ old_id ^ "\n") in
	      return new_op_renaming
	    else
	      % let _ = toScreen("\nTranslating op info for " ^ old_q ^ "." ^ old_id ^ "\n") in
	      {
	       new_names <- foldM (fn new_qids -> fn old_qid ->
				   foldM (fn new_qids -> fn new_qid ->
					  if member (new_qid, new_qids) then
					    return new_qids
					  else 
					    return (Cons (new_qid, new_qids)))
				         new_qids
					 (translateOpQualifiedIdToAliases op_renaming old_qid))
	                          [] 
				  old_info.names;
	       new_names <- return (rev new_names);
	       new_info <- foldM (fn merged_info -> fn (Qualified (new_q, new_id)) ->
				  mergeOpInfo merged_info 
					      (findAQualifierMap (new_op_renaming, new_q, new_id))
					      position)
	                         (old_info << {names = new_names})
				 new_names;
	       foldM (fn new_op_renaming -> fn (Qualified (new_q, new_id)) ->
		      % let _ = toScreen("\n  Inserting op info for " ^ new_q ^ "." ^ new_id ^ "\n") in
		      return (insertAQualifierMap (new_op_renaming, new_q, new_id, new_info)))
	             new_op_renaming  
		     new_names
	      }
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_ops 

      def translateSortMap old_sorts =
        let 
          def translateStep (old_q, old_id, old_info, new_sort_renaming) =
	    let Qualified (primary_q, primary_id) = primarySortName old_info in
	    if ~ (old_q = primary_q && old_id = primary_id) then
	      % let _ = toScreen("\nIgnoring sort info for " ^ old_q ^ "." ^ old_id ^ "\n") in
	      return new_sort_renaming
	    else
	      % let _ = toScreen("\nTranslating sort info for " ^ old_q ^ "." ^ old_id ^ "\n") in
	      {
	       new_names <- foldM (fn new_qids -> fn old_qid ->
				   foldM (fn new_qids -> fn new_qid ->
					  if member (new_qid, new_qids) then
					    return new_qids
					  else 
					    return (Cons (new_qid, new_qids)))
				         new_qids
					 (translateSortQualifiedIdToAliases sort_renaming old_qid))
	                          [] 
				  old_info.names;
	       new_names <- return (rev new_names);
	       if member (unqualified_Boolean, new_names) || member (Boolean_Boolean, new_names) then
		 return new_sort_renaming
	       else
		{ 
		 new_info <- foldM (fn merged_info -> fn (Qualified (new_q, new_id)) ->
				     mergeSortInfo merged_info 
						   (findAQualifierMap (new_sort_renaming, new_q, new_id))
						   position)
				    (old_info << {names = new_names})
				    new_names;
		  foldM (fn new_sort_renaming -> fn (Qualified (new_q, new_id)) ->
			 % let _ = toScreen("\n  Inserting sort info for " ^ new_q ^ "." ^ new_id ^ "\n") in
			 return (insertAQualifierMap (new_sort_renaming, new_q, new_id, new_info)))
		        new_sort_renaming  
			new_names 
		}}
	in
	  foldOverQualifierMap translateStep emptyAQualifierMap old_sorts 

    in
    let s2 as {sorts, ops, elements, qualified?}
         = 
         mapSpec (translateOp op_renaming, translateSort sort_renaming, translatePattern) spc
    in 
    let 
      def translateElements elements =
	mapSpecElements (fn el ->
			 case el of
			   | Op      qid -> Op      (translateOpQualifiedId op_renaming qid)
			   | OpDef   qid -> OpDef   (translateOpQualifiedId op_renaming qid) 
			   | Sort    qid -> Sort    (translateOpQualifiedId sort_renaming qid) 
			   | SortDef qid -> SortDef (translateOpQualifiedId sort_renaming qid)
			   | Property (pt, nm, tvs, term) ->
			     Property (pt, (translateOpQualifiedId op_renaming nm), tvs, term)
			   | Import (sp_tm, spc, els) ->  
			     %% The Import expression we have just dispatched on was constructed 
			     %% by mapSpecElements.  In particular, els was constructed by 
			     %% applying this fn to each of the original imported elements. 
			     %% So we don't want to recur again here, but we do want to tweak 
			     %% the term:
			     Import (case opt_renaming_expr of
				       | Some renaming_expr ->
				         (Translate (sp_tm, renaming_expr), noPos)
				       | _ -> sp_tm,
				     spc,
				     els)
			   | _ -> el)
                        elements
    in
    {
     newSorts <- translateSortMap sorts;
     newOps   <- translateOpMap   ops;
     return {sorts      = newSorts,
	     ops        = newOps,
	     elements   = translateElements elements,
	     qualified? = false}	% conservative
    }

endspec
\end{spec}
