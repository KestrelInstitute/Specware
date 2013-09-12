
%% TODO: This has file suffers greatly from having to accommodate the representation
%% of specs, ops, types and ids. 
%% 
%% Also the parser seems to set up a cod_aliases field. I would argue that
%% this should be removed from the parser. I disagree. I, on the other hand,
%% agree with myself. I couldn't agree more.

SpecCalc qualifying spec

  import /Languages/MetaSlang/Specs/CompressSpec

  import Signature                                  % including SCTerm
  import UnitId/Utilities                           % for uidToString, if used...

  import Spec/AccessSpec
  import Spec/MergeSpecs
  import Spec/VarOpCapture
  import Spec/ComplainIfAmbiguous

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  type Translators = {ambigs : Translator,
		      types  : Translator,
		      ops    : Translator,
		      props  : Translator,
		      others : Option OtherTranslators}

  type Translator = AQualifierMap (QualifiedId * Aliases) 

  op  emptyTranslator : Translator
  def emptyTranslator = emptyAQualifierMap

  type OtherTranslators

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% Perhaps evaluating a translation should yield a morphism rather than just 
  %% a spec. Then perhaps we add dom and cod domain operations on morphisms.
  %% Perhaps the calculus is getting too complicated.

  def SpecCalc.evaluateTranslate term renaming pos = 
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating spec-translation at " ^ uidToString unitId ^ "\n");
     value_info as (value, ts, uids) <- evaluateTermInfo term;
     case coerceToSpec value of
       | Spec spc -> 
         {
	  new_spec <- translateSpec true spc renaming [] false (Some unitId);
	  new_spec <- complainIfAmbiguous new_spec pos;
	  raise_any_pending_exceptions;  % should never happen, but...
	  return (Spec new_spec, ts, uids)
	 }
       | Other _ ->
	 evaluateOtherTranslate term value_info renaming pos
       | _ -> 
	 raise (TypeCheck (pos, "translating a term that is not a specification"))
    }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% To translate a spec means to recursively descend the hierarchy of imports
  %% and translate names. This can raise exceptions since ops may end up with
  %% the same names.
  %% 
  %% If the following, assume we are given the rule "<lhs> +-> <rhs>"
  %% 
  %% We lookup <lhs> in the domain spec to find a domain item, raising an exception
  %% if nothing can be found.  The rules are intended to be the same as those used
  %% when linking names in formulas within a spec, but the keywords "type" and "op" 
  %% are allowed here to disambiguate an otherwise missing context:
  %% 
  %%   "type [A.]X"   will look at types only
  %%   "op   [A.]X"   will look at ops   only
  %%   "[A.]X"        will look at types and ops, raising an exception if there are both
  %%   "[A.]f : B.X"  will lookup [A.]f of type [B.]X
  %%   "X"            will find unqualified "X" in preference to "A.X" if both exist.
  %% 
  %% Translate all references to the found item into <rhs>, with the following
  %% caveats:
  %% 
  %%  If <rhs> lacks an explicit qualifier, the rhs item is unqualified.
  %% 
  %%  Multiple lhs items may not map to the same rhs item.
  %% 
  %% Note: The code below does not yet match the documentation above, but should.
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% translateSpec is used by Translate and Colimit
  op  translateSpec : Bool -> Spec -> Renaming -> QualifiedIds -> Bool -> Option UnitId -> Env Spec
  def translateSpec allow_exceptions? spc renaming immune_op_names allow_extra_rules? currentUID? = 
    %%
    %% WARNING:  When allow_exceptions? is false, as when called from colimit,
    %% translateSpec (and the routines it calls) must not raise any errors,
    %% either directly or deferred.  I.e., we may call raise and/or raise_later
    %% only if require_monic? is true.
    %%
    %% The colimit code invokes the monad produced here through a special 
    %% call to run that is not prepared to handle exceptions.
    %%
    let pos = positionOf renaming in
    {
     translators <- makeTranslators allow_exceptions? spc renaming immune_op_names allow_extra_rules?;
     when allow_exceptions?
      raise_any_pending_exceptions;
     %% translators is now an explicit map for which each name in its 
     %% domain refers to a particular type or op in the domain spec.  
     %%
     %% Each rule explicitly states that it is mapping a type or an op, 
     %% and there are no wildcards.   
     %%
     %% No two lhs items (types or ops) map to the same rhs item.
     %%
     %% makeTranslators will have raised various exceptions if it 
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
     spc <- auxTranslateSpec spc translators currentUID? (Some renaming);
     return spc
    } 

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  makeTranslators : Bool -> Spec -> Renaming -> QualifiedIds -> Bool -> SpecCalc.Env Translators
  def makeTranslators allow_exceptions? dom_spec (renaming_rules, position) immune_op_names allow_extra_rules? =
    %% translateSpec is used by Translate and Colimt
    %% When called from Colimit, allow_exceptions? is false, and we should avoid
    %% raising exceptions...
    let types = dom_spec.types in
    let ops   = dom_spec.ops   in
    let 

      def complain_if_type_collision (types, type_translator, this_dom_q, this_dom_id, this_new_qid, rule_pos) =
	let collisions =
	    foldriAQualifierMap (fn (other_dom_q, other_dom_id, other_target, collisions) ->
				 case other_target of
				   | (other_new_qid, _) ->
				     if other_new_qid = this_new_qid then
				       let other_dom_qid = Qualified (other_dom_q, other_dom_id) in
				       let Some this_info = findAQualifierMap (types, this_dom_q, this_dom_id) in
				       if other_dom_qid in? this_info.names then
					 %% ok to map aliases to same new name
					 collisions
				       else
					 %% not legal to map unrelated type names to the same new name
					 collisions ++ [other_dom_qid]
				     else
				       collisions)
	                        []
				type_translator
	in
	 case collisions of
	   | [] -> return ()
	   | _ ->
	     let conflicting_names = 
	         case collisions of
		   | [name] -> " and type " ^ (explicitPrintQualifiedId name)
		   | first::rest ->
		     " and types " ^ (explicitPrintQualifiedId first) ^
		     (foldl (fn (str, qid) -> str ^ ", " ^ explicitPrintQualifiedId qid)
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

      def complain_if_op_collision (ops, op_translator, this_dom_q, this_dom_id, this_new_qid, rule_pos) =
	let collisions =
	    foldriAQualifierMap (fn (other_dom_q, other_dom_id, other_target, collisions) ->
				 case other_target of
				   | (other_new_qid, _) ->
				     if other_new_qid = this_new_qid then
				       let other_dom_qid = Qualified (other_dom_q, other_dom_id) in
				       let Some this_info = findAQualifierMap (ops, this_dom_q, this_dom_id) in
				       if other_dom_qid in? this_info.names then
					 %% ok to map aliases to same new name
					 collisions
				       else
					 %% not legal to map unrelated type names to the same new name
					 collisions ++ [other_dom_qid]
				     else
				       collisions)
	                        []
				op_translator
	in
	 case collisions of
	   | [] -> return ()
	   | _ ->
	     let conflicting_names = 
	         case collisions of
		   | [name] -> " and op " ^ (explicitPrintQualifiedId name)
		   | first::rest ->
		     " and ops " ^ (explicitPrintQualifiedId first) ^
		     (foldl (fn (str, qid) -> str ^ ", " ^ explicitPrintQualifiedId qid)
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

      def complain_if_type_collisions_with_priors (types, type_translator) =
	foldOverQualifierMap (fn (dom_q, dom_id, (new_qid as Qualified(new_q,new_id),_), _) ->
			      %% we're proposing to translate dom_q.dom_id into new_q.new_id
			      case findAQualifierMap (types, new_q, new_id) of
				| None -> 
				  %% new_q.new_id does not refer to a pre-existing type, so we're ok
				  return ()
				| Some prior_info -> 
				  %% new_q.new_id refers to a pre-existing type
				  case findAQualifierMap (type_translator, new_q, new_id) of
				    | Some _ -> 
				      %% but we're translator new_q.new_id out of the way, so we're ok
				      return ()
				    | None ->
				      %% new_q.new_id refers to a pre-existing type, and is not being renamed away
				      if Qualified(dom_q, dom_id) in? prior_info.names then
					%% but it's an alias of dom_q.dom_id, so we're just collapsing aliases to the same name
					return () 
				      else
					%% new_q, new_id is a pre-existing, untranslated, non-alias type
					raise_later (TranslationError ("Illegal to translate type " ^ (explicitPrintQualifiedId (Qualified(dom_q,dom_id))) ^
								       " into pre-existing, non-alias, untranslated " ^ (explicitPrintQualifiedId new_qid),
								       position)))
	                     ()
			     type_translator


      def complain_if_op_collisions_with_priors (ops, op_translator) =
	foldOverQualifierMap
          (fn (dom_q, dom_id, (new_qid as Qualified(new_q,new_id),_), _) ->
              %% we're proposing to translate dom_q.dom_id into new_q.new_id
            case findAQualifierMap (ops, new_q, new_id) of
              | None -> 
                %% new_q.new_id does not refer to a pre-existing op, so we're ok
                return ()
              | Some prior_info -> 
                %% new_q.new_id refers to a pre-existing op
                case findAQualifierMap (op_translator, new_q, new_id) of
                  | Some _ -> 
                    %% but we're translator new_q.new_id out of the way, so we're ok
                    return ()
                  | None ->
                    %% new_q, new_id refers to a pre-existing op, and is not being renamed away
                    if Qualified(dom_q,dom_id) in? prior_info.names then
                      %% but it's an alias of dom_q.dom_id, so we're just collapsing aliases to the same name
                      return ()
                    else
                      %% new_q,new_id refers to pre-existing, untranslated, non-alias op 
                      raise_later (TranslationError ("Illegal to translate op "
                                                       ^ (explicitPrintQualifiedId (Qualified(dom_q,dom_id)))
                                                       ^ " into pre-existing, non-alias, untranslated "
                                                       ^ (explicitPrintQualifiedId new_qid),
                                                     position)))
            ()
            op_translator


      def insert (op_translator, type_translator) (renaming_rule, rule_pos) =

	let 
          def add_type_rule op_translator type_translator (dom_qid as Qualified (dom_q, dom_id))
                dom_types cod_qid cod_aliases =
	    case dom_types of
	      | first_info :: other_infos ->
	        (let primary_dom_qid as Qualified (primary_q, primary_id) = primaryTypeName first_info in
		 if other_infos = [] || primary_q = UnQualified then
		  %% dom_qid has a unique referent, either because it refers to 
		  %% exactly one type, or becauses it is unqualified and refers 
		  %% to an unqualified type (perhaps among others), in which 
		  %% case that unqualified type is (by language definition) 
		  %% the unique unique referent.  
		  %% (Note that a qualified dom_qid can't refer to an unqualified 
		  %% type, so we can suppress the test for unqualified dom_qid.)						     
		  if basicTypeName? primary_dom_qid then
		    {raise_later (TranslationError ("Illegal to translate from base type : "
                                                      ^ (explicitPrintQualifiedId dom_qid),
						    rule_pos));
		     return (op_translator, type_translator)
		    }
		  else
		    case findAQualifierMap (type_translator, dom_q, dom_id) of
		      | None -> 
		        {when allow_exceptions?
			   (complain_if_type_collision
                              (types, type_translator, dom_q, dom_id, cod_qid, rule_pos));
			 new_type_translator
                           <- return (insertAQualifierMap
                                        (type_translator, dom_q, dom_id, (cod_qid, cod_aliases)));
			 new_type_translator
                           <- return (if dom_q = UnQualified && primary_q ~= UnQualified && dom_id = primary_id then
                                        %% in rule X +-> Y, X refers to A.X
                                        %% so both X and A.X should translate to Y
                                        insertAQualifierMap
                                          (new_type_translator, primary_q, primary_id, (cod_qid, cod_aliases))
                                      else 
                                        new_type_translator);
			 return (op_translator, new_type_translator)
			 }
		      | _  -> 
			{raise_later (TranslationError ("Multiple rules for source type "
                                                          ^ (explicitPrintQualifiedId dom_qid),
							rule_pos));
			 return (op_translator, type_translator)
			}
		else 
		  {
		   raise_later (TranslationError ("Ambiguous source type " ^ (explicitPrintQualifiedId dom_qid), 
						  rule_pos));
		   return (op_translator, type_translator)
		  })
	      | _ -> 
		if allow_extra_rules? then
		  return (op_translator, type_translator)
		else
		  {
		   raise_later (TranslationError ("Unrecognized source type " ^ (explicitPrintQualifiedId dom_qid),
						  rule_pos));
		   return (op_translator, type_translator)
		  }
		  
	      
	  def add_op_rule op_translator type_translator (dom_qid as Qualified(dom_q, dom_id)) dom_ops cod_qid cod_aliases =
	    case dom_ops of
	      | first_op :: other_ops ->
	        (let primary_dom_qid as Qualified (primary_q, primary_id) = primaryOpName first_op in
		 if other_ops = [] || primary_q = UnQualified then
		   %% See note above for types.
		   if basicOpName? primary_dom_qid then
		     {
		      raise_later (TranslationError ("Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid),
						     rule_pos));
		      return (op_translator, type_translator)
		     }
		   else
		     case findAQualifierMap (op_translator, dom_q, dom_id) of
		       
		       | None -> 
		         %% No rule yet for dom_qid...
		         {
			  when allow_exceptions?
			   (complain_if_op_collision (ops, op_translator, dom_q, dom_id, cod_qid, rule_pos));
			  new_op_translator <- return (insertAQualifierMap (op_translator, dom_q, dom_id, (cod_qid, cod_aliases)));
			  new_op_translator <- return (if dom_q = UnQualified && primary_q ~= UnQualified && dom_id = primary_id then
						  %% in rule X +-> Y, X refers to A.X
						  %% so both X and A.X should translate to Y
						  insertAQualifierMap (new_op_translator, primary_q, primary_id, (cod_qid, cod_aliases))
						else 
						  new_op_translator);
			  return (new_op_translator, type_translator)
			  }
		       | _ -> 
			 %% Already had a rule for dom_qid...
			 {
			  raise_later (TranslationError ("Multiple rules for source op "^
							 (explicitPrintQualifiedId dom_qid),
							 rule_pos));
			  return (op_translator, type_translator)
			 }
		 else 
		   {
		    raise_later (TranslationError ("Ambiguous source op " ^ (explicitPrintQualifiedId dom_qid),
						   rule_pos));
		    return (op_translator, type_translator)
		    })
	      | _ -> 
		if allow_extra_rules? then
		  return (op_translator, type_translator)
		else
		  {
		   raise_later (TranslationError ("Unrecognized source op " ^ (explicitPrintQualifiedId dom_qid),
						  rule_pos));
		   return (op_translator, type_translator)
		  }
		  
	  def add_wildcard_rules op_translator type_translator dom_q cod_q cod_aliases =
	    %% Special hack for aggregate translators: X._ +-> Y._
	    %% Find all dom types/ops qualified by X, and requalify them with Y
	    (if basicQualifier? dom_q then
	       {
		raise_later (TranslationError ("Illegal to translate from base : " ^ dom_q, 
					       position));
		return (op_translator, type_translator)
		}
	     else
	       let

		 def extend_type_translator (type_q, type_id, _ (* type_info *), type_translator) =
		   if type_q = dom_q then
		     %% This is a candidate to be translated...
		     case findAQualifierMap (type_translator, type_q, type_id) of
		       | None -> 
		         %% No rule yet for this candidate...
		         let new_cod_qid = mkQualifiedId (cod_q, type_id) in
			 {
			  when allow_exceptions? 
			   (complain_if_type_collision (types, type_translator, type_q, type_id, new_cod_qid, rule_pos));
			  return (insertAQualifierMap (type_translator, type_q, type_id, (new_cod_qid, [new_cod_qid])))
			 }
		       | _ -> 
			 {
			  raise_later (TranslationError ("Multiple (wild) rules for source type "^
							 (explicitPrintQualifiedId (mkQualifiedId (type_q, type_id))),
							 rule_pos));
			  return type_translator
			  }
		   else
		     return type_translator

                 def extend_op_translator (op_q, op_id, _ (* op_info *), op_translator) =
		   if op_q = dom_q then
		     %% This is a candidate to be translated...
		     case findAQualifierMap (op_translator, op_q, op_id) of
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
			  when allow_exceptions? 
			   (complain_if_op_collision (ops, op_translator, op_q, op_id, new_cod_qid, rule_pos));
			  return (insertAQualifierMap (op_translator, op_q, op_id, (new_cod_qid, [new_cod_qid])))
			 }
		       | _ -> 
			 %% Candidate already has a rule (e.g. via some explicit mapping)...
			 {
			  raise_later (TranslationError ("Multiple (wild) rules for source op "^
							 (explicitPrintQualifiedId (mkQualifiedId (op_q, op_id))),
							 rule_pos));
			  return op_translator
			  }
						  
		   else
		     return op_translator 
	       in 
		 {
		  %% Check each dom type and op to see if this abstract ambiguous rule applies...
		  type_translator <- foldOverQualifierMap extend_type_translator type_translator types;
		  op_translator   <- foldOverQualifierMap extend_op_translator   op_translator   ops;
		  return (op_translator, type_translator)
		 })

    in
      case renaming_rule of
	
	%% TODO: ?? Add special hack for aggregate type translators: X._ +-> Y._  ??
	%% TODO: ?? Add special hack for aggregate op   translators: X._ +-> Y._  ??

        | Type (dom_qid, cod_qid, cod_aliases) -> 
	  if basicTypeName? dom_qid then
	    {
	     raise_later (TranslationError ("Illegal to translate from base type : " ^ (explicitPrintQualifiedId dom_qid),
					    rule_pos));
	     return (op_translator, type_translator)
	    }
	  else 
	    let dom_types = findAllTypes (dom_spec, dom_qid) in
	    add_type_rule op_translator type_translator dom_qid dom_types cod_qid cod_aliases

	| Op   ((dom_qid, dom_type), (cod_qid, cod_type), cod_aliases) ->  
	  if syntactic_qid? dom_qid then 
	    {
	     raise_later (TranslationError ("`" ^ (explicitPrintQualifiedId dom_qid) ^ "' is syntax, not an op, hence cannot be translated.",
					    rule_pos));
	     return (op_translator, type_translator)
	    }
	  else if basicOpName? dom_qid then
	    {
	     raise_later (TranslationError ("Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid),
					    rule_pos));
	     return (op_translator, type_translator)
	    }
	  else if dom_qid in? immune_op_names then
	    return (op_translator, type_translator)
	  else 
	    let dom_ops = findAllOps (dom_spec, dom_qid) in
	    add_op_rule op_translator type_translator dom_qid dom_ops cod_qid cod_aliases

	| Ambiguous (Qualified(dom_q, "_"), Qualified(cod_q,"_"), cod_aliases) -> 
	  add_wildcard_rules op_translator type_translator dom_q cod_q cod_aliases

	| Ambiguous (dom_qid, cod_qid, cod_aliases) -> 
	  if syntactic_qid? dom_qid then 
	    {
	     raise_later (TranslationError ("`" ^ (explicitPrintQualifiedId dom_qid)
                                              ^ "' is syntax, not an op, hence cannot be translated.",
					    rule_pos));
	     return (op_translator, type_translator)
	     }
	  else if basicQualifiedId? dom_qid then
	    {
	     raise_later (TranslationError ("Illegal to translate from base type or op: "
                                              ^ (explicitPrintQualifiedId dom_qid),
					    rule_pos));
	     return (op_translator, type_translator)
	     }
	  else
	    %% Find a type or an op, and proceed as above
	    let dom_types = findAllTypes (dom_spec, dom_qid) in
	    let dom_ops   = if dom_qid in? immune_op_names then [] else findAllOps (dom_spec, dom_qid) in
	    case (dom_types, dom_ops) of
	      | ([], []) ->
                {
                 if dom_qid in? immune_op_names
                      && ~ (empty? (findAllOps (dom_spec, dom_qid))) then
                   raise_later (TranslationError ("Source op "
                                                    ^(explicitPrintQualifiedId dom_qid)
                                                    ^ " is immune to translation", 
                                                  rule_pos))
                 else
                   if allow_extra_rules? then
                     return ()
                   else
                     raise_later (TranslationError ("Unrecognized source type or op "
                                                      ^(explicitPrintQualifiedId dom_qid), 
                                                    rule_pos));
                     return (op_translator, type_translator)
                     }
	      | (_,  []) -> add_type_rule op_translator type_translator dom_qid dom_types cod_qid cod_aliases
	      | ([], _)  -> add_op_rule   op_translator type_translator dom_qid dom_ops   cod_qid cod_aliases
	      | (_,  _)  -> {
			     raise_later (TranslationError ("Ambiguous source type or op: "^(explicitPrintQualifiedId dom_qid),
							    rule_pos));
			     return (op_translator, type_translator)
			    }
    in
      {
       (op_translator, type_translator) <- foldM insert (emptyTranslator, emptyTranslator) renaming_rules;
       when allow_exceptions?
        {complain_if_type_collisions_with_priors (types, type_translator);
	 complain_if_op_collisions_with_priors   (ops, op_translator)};
       return {
	       ambigs = emptyTranslator,
	       types  = type_translator,
	       ops    = op_translator, 
	       props  = op_translator,   % TODO: make this distinct
	       others = None
	      }
       }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def basicCodTypeName? qid =
    let base_spec = getBaseSpec () in
    case findAllTypes (base_spec, qid) of
      | [] -> false
      | _  -> true

  def basicCodOpName? qid =
    let base_spec = getBaseSpec () in
    case findAllOps (base_spec, qid) of
      | [] -> false
      | _  -> true

  def basicCodName? qid =
    let base_spec = getBaseSpec () in
    case findAllTypes (base_spec, qid) of
      | [] ->
        (case findAllOps (base_spec, qid) of
	   | [] -> false
	   | _  -> true)
      | _ -> true

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% auxTranslateSpec is used by Translate, Substitute, and (indirectly) Colimt
  %% It should avoid raising any errors.
  %% In particular, if an operation such as translate wishes to signal errors in 
  %% some situations, those errors should be raised while Translators is being 
  %% created, not here.
  op  auxTranslateSpec : Spec -> Translators -> Option UnitId -> Option Renaming -> SpecCalc.Env Spec
  def auxTranslateSpec spc translators currentUID? opt_renaming =
    let type_translator = translators.types in
    let   op_translator = translators.ops   in
    %% TODO: need to avoid capture that occurs for "X +-> Y" in "fa (Y) ...X..."
    %% TODO: ?? Change UnQualified to new_q in all qualified names ??
    let

      def translateQualifiedIdToAliases translator (qid as Qualified (q, id)) =
        case findAQualifierMap (translator, q,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translateTypeInfos old_types =
        let 
          def translateTypeInfo (q, id, info, types) =
	    let Qualified (primary_q, primary_id) = primaryTypeName info in
	    if ~ (q = primary_q && id = primary_id) then
	      return types
	    else
	      {
	       new_names <- foldM (fn new_qids -> fn old_qid ->
				   foldM (fn new_qids -> fn new_qid ->
					  if new_qid in? new_qids then
					    return new_qids
					  else 
					    return (Cons (new_qid, new_qids)))
				         new_qids
					 (translateQualifiedIdToAliases type_translator old_qid))
	                          [] 
				  info.names;
	       new_names <- return (reverse new_names);
	       if unqualified_Boolean in? new_names || Boolean_Boolean in? new_names then
		 return types
	       else
		 let new_info = info << {names = new_names} in
		 return (mergeTypeInfo spc types new_info)
	      }
	in
	  foldOverQualifierMap translateTypeInfo emptyAQualifierMap old_types 

      def translateOpInfos old_ops =
        let 
          def translateOpInfo (q, id, info, ops) =
	    let Qualified (primary_q, primary_id) = primaryOpName info in
	    if ~ (q = primary_q && id = primary_id) then
	      return ops
	    else
	      {
	       new_names <- foldM (fn new_qids -> fn old_qid ->
				   foldM (fn new_qids -> fn new_qid ->
					  if new_qid in? new_qids then
					    return new_qids
					  else 
					    return (Cons (new_qid, new_qids)))
				         new_qids
					 (translateQualifiedIdToAliases op_translator old_qid))
	                          [] 
				  info.names;
	       new_names <- return (reverse new_names);
	       let new_info = info << {names = new_names} in
	       return (mergeOpInfo spc ops new_info)
	      }
	in
	  foldOverQualifierMap translateOpInfo emptyAQualifierMap old_ops 

    in
    let s = mapSpec (translateOpRef   op_translator, 
		     translateTypeRef type_translator, 
		     translatePattern)
                    spc
    in
    {
     new_types    <- translateTypeInfos s.types;
     new_ops      <- translateOpInfos   s.ops;
     new_elements <- return (translateSpecElements translators opt_renaming s.elements currentUID?);
     new_spec     <- return (markQualifiedStatus{types     = new_types,
                                                 ops       = new_ops,
                                                 elements  = new_elements,
                                                 qualifier = None});	

     %% Next we worry about traditional captures in which a (global) op Y,
     %% used under a binding of var X, is renamed to X.   Internally, this 
     %% is not a problem, since the new refs to op X are distinguishable 
     %% from the refs to var X, but printing the resulting formula loses
     %% that distinction, so refs to the op X that are under the binding 
     %% of var X would be read back in as refs to the var X.
     %% 
     %% So we do alpha conversions if a bound var has an op of the same
     %% name under its scope:
     new_spec     <- return (removeVarOpCaptures new_spec);
     % new_spec     <- return (compressDefs        new_spec);
     return new_spec
    }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  translateQualifiedId : Translator -> QualifiedId -> QualifiedId
  op  translateTypeRef     : Translator -> MSType -> MSType
  op  translateOpRef       : Translator -> MSTerm -> MSTerm
  op  translatePattern     : MSPattern  -> MSPattern

  def translateQualifiedId translator (qid as Qualified (q, id)) =
    case findAQualifierMap (translator, q,id) of
      | Some (nQId,_) -> nQId
      | None -> qid

  def translateTypeRef type_translator type_term =
    case type_term of
      | Base (qid, srts, pos) ->
	(let new_qid = translateQualifiedId type_translator qid in
	 if new_qid = qid then type_term else Base (new_qid, srts, pos))
      | _ -> type_term

  def translateOpRef op_translator op_term =
    case op_term of
      | Fun (Op (qid, fixity), srt, pos) ->
	(let new_qid = translateQualifiedId op_translator qid in
	 if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, pos))
      | _ -> op_term

  def translatePattern pat = pat

  op  translateSpecElements : Translators -> Option Renaming -> SpecElements -> Option UnitId -> SpecElements
  def translateSpecElements translators opt_renaming elements currentUID? =
    let base = getBaseSpec() in
    map (translateSpecElement translators opt_renaming currentUID? base) elements

  op  translateSpecElement : Translators -> Option Renaming -> Option UnitId -> Spec -> SpecElement -> SpecElement
  def translateSpecElement translators opt_renaming currentUID? base el =
    case el of
      | Type    (qid, a)       -> Type    (translateQualifiedId translators.types qid, a) 
      | TypeDef (qid, a)       -> TypeDef (translateQualifiedId translators.types qid, a)
      | Op      (qid, def?, a) -> Op      (translateQualifiedId translators.ops   qid, def?, a)
      | OpDef   (qid, refine?, hist, a) -> OpDef(translateQualifiedId translators.ops   qid, refine?, hist, a)
      | Property (pt, nm, tvs, term, a) ->
        Property (pt, (translateQualifiedId translators.props nm), tvs, term, a)
      | Import (sp_tm, spc, els, a) ->  
        let els = translateSpecElements translators opt_renaming els currentUID? in
	let (new_tm, spc, els) =
            if spc = base
              then (sp_tm, spc, els)
            else
	    case opt_renaming of
	      | Some (rules, pos) ->
	        let rules = foldl (fn (rules, rule) ->
				   case rule of
				     | (Type (dom_qid, _, _), _) ->
				       (case findTheType (spc, dom_qid) of
					  | Some _ -> [rule] ++ rules
					  | _ -> rules)
				     | (Op ((dom_qid, _), _, _), _) ->
				       (case findTheOp (spc, dom_qid) of
					  | Some _ -> rule :: rules
					  | _ -> rules)
                                     | (Ambiguous (dom_qid, _, _), _) ->
                                          if someNonBaseType? (spc, dom_qid, base) || someNonBaseOp? (spc, dom_qid, base) then
                                            [rule] ++ rules
                                          else
                                            rules
				     | _ -> 
                                       %% can we translate anything besides type or op?
				       [rule] ++ rules)
		                  []
				  rules
		in
                % let _ = writeLine("Translate import\n"^anyToString sp_tm^"\n"^anyToString rules) in
                (case rules of
                   | [] -> (sp_tm, spc, els)
                   | _ ->
                     let renaming = (reverse rules, pos) in
                     let trans_spc_tm = (Translate (sp_tm, renaming), pos) in
                      let _ = writeLine("trans_spc_tm:\n"^anyToString trans_spc_tm) in
                      let _ = writeLine("currentUID?:\n"^anyToString currentUID?) in
                     case UIDfromPosition(sp_tm.2) of
                       | None -> (trans_spc_tm, spc, els)
                       | Some currentUID ->
                     case evaluateTermWrtUnitId(trans_spc_tm, currentUID) of
                       | Some(Spec trans_spc) ->
                          let _ = writeLine("trans_spc:\n"^anyToString trans_spc) in
                         (trans_spc_tm, trans_spc, els)
                       | None ->
                         % let _ = writeLine("Failed to evaluate translate:\n"
                         %                     ^showSCTerm trans_spc_tm) in
                         % let _ = writeLine("wrt tUID:\n"^anyToString currentUID) in
                         (trans_spc_tm, spc, els))
              | _ -> (sp_tm, spc, els)
	in
        Import (new_tm, spc, els, a)
      | _ -> el

 op someNonBaseType? (spc : Spec, Qualified (q, id) : QualifiedId, base : Spec) : Bool = 
   if q = UnQualified then
     case findAQualifierMap (spc.types, q, id) of
       | Some info -> true
       | None      -> false
   else
     let spec_srts = wildFindUnQualified (spc.types, id) in
     if spec_srts = [] then
       false
     else
      let base_srts = wildFindUnQualified (base.types, id) in
      forall? (fn spec_srt -> ~ (spec_srt in? base_srts)) spec_srts

 op someNonBaseOp? (spc : Spec, Qualified (q, id) : QualifiedId, base : Spec) : Bool = 
   if q = UnQualified then
     case findAQualifierMap (spc.ops, q, id) of
       | Some info -> true
       | None      -> false
   else
     let spec_ops = wildFindUnQualified (spc.ops, id) in
     if spec_ops = [] then
       false
     else
      let base_ops = wildFindUnQualified (base.ops, id) in
      forall? (fn spec_op-> ~ (spec_op in? base_ops)) spec_ops

% op  Specware.cleanEnv : SpecCalc.Env ()
% op  Specware.runSpecCommand : [a] SpecCalc.Env a -> a
op  evaluateTermWrtUnitId(sc_tm: SCTerm, currentUID: UnitId): Option Value = 
  let
    %% Ignore exceptions
    def handler except =
      return None
  in
  let prog = {%cleanEnv;
              saveUID <- getCurrentUID;
              setCurrentUID currentUID;
              val  <- evaluateTerm sc_tm;
              % print ("evalTerm:\n"^(case val of Spec spc -> printSpec spc | _ -> "")^"\n" );
              setCurrentUID saveUID;
              return (Some val)} 
  in
    run (catch prog handler)   % toplevelHandlerOption

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  ppTranslators : Translators -> Doc
  def ppTranslators translators =
    let docs = (ppTranslatorMap (ppString "")          translators.ambigs) ++ 
               (ppTranslatorMap (ppString "type ")     translators.types)  ++ 
               (ppTranslatorMap (ppString "op ")       translators.ops)    ++
               (ppTranslatorMap (ppString "property ") translators.props)  ++
	       (case translators.others of
		  | None -> []
		  | Some other -> ppOtherTranslators other)
    in
    ppConcat [ppString "{",
	      ppSep (ppString ", ") docs,
	      ppString "}"]

  op  ppTranslatorMap : Doc -> Translator -> List Doc
  def ppTranslatorMap type_or_op translator =
    foldriAQualifierMap (fn (dom_q, dom_id, (cod_qid as Qualified(cod_q, cod_id), _), docs) ->
			 if dom_q = cod_q && dom_id = cod_id then
			   %% don't print identity rules ...
			   docs
			 else
			   [ppConcat [type_or_op,
				      ppQualifier (Qualified(dom_q, dom_id)),
				      ppString " +-> ",
				      ppQualifier cod_qid]]
			   ++ docs)
                        []
			translator

  op ppOtherTranslators : OtherTranslators -> List Doc

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
