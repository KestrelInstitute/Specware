SpecCalc qualifying spec
{
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import Translate                                    % for auxTranslateSpec % ??
  import SpecUnion                                    % for specUnion
  import SpecSubst                                    % for warnAboutMissingItems, SCTerm
  import Print                                        % for printMorphism
  % import TypeCoercer                                % for addCoercions
  import /Library/Unvetted/Random                     % for random

  op applySpecPrismSubstitution (prsm          : SpecPrism)
                                (original_spec : Spec) 
                                (prism_tm      : SCTerm) 
                                (term_pos      : Position) 
   : SpecCalc.Env Spec =                          
   {
    verify_subspec prsm.dom original_spec term_pos;
    auxApplySpecPrismSubstitution prsm original_spec prism_tm term_pos
    }

  op auxApplySpecPrismSubstitution (prsm     : SpecPrism)
                                   (spc      : Spec) 
                                   (prism_tm : SCTerm) 
                                   (pos      : Position) 
   : SpecCalc.Env Spec =                          
   % (p as {dom, sms, pmode, tm}) 
   case prsm.pmode of
     | Uniform s ->
       (case s of
          | Random     -> applySpecPrismSubstitutionRandom     prsm spc pos 
          | Generative -> applySpecPrismSubstitutionGenerative prsm spc pos 
          | Nth n      -> 
            if n < length prsm.sms then
              applySpecPrismSubstitutionNth prsm n spc pos
            else
              let _ = writeLine("Error: Attempted to select sm \#" ^ anyToString n ^
                                  ", but there are only " ^ anyToString (length prsm.sms) ^ 
                                  " morphisms in prism -- ignoring substitution.") 
              in
              return spc)
     | PerInstance _ ->
       applySpecPrismSubstitutionPerInstance prsm spc pos 
	  
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% Choose one sm and use it uniformly
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def applySpecPrismSubstitutionRandom prsm spc pos =
    let n = random (length prsm.sms) in
    applySpecPrismSubstitutionNth prsm n spc pos

  def applySpecPrismSubstitutionGenerative prsm spc pos =
    let prism_tm = prsm.tm in
    {
     uid    <- getCurrentUID;
     status <- getPrismStatus; % get from environment
     choice <- (case findLeftmost (fn choice -> prism_tm = choice.prism_tm) status.choices of
                  | None ->
                    {
                     %% Installing initial choice for prism_tm.
                     choice <- return {uid = uid, prism_tm = prism_tm, n = 0};
                     setPrismStatus (status << {choices = status.choices ++ [choice]}); % record in environment
                     return choice
                     }
                  | Some choice ->
                    %% Fetching stored choice for prism_tm.
                    %% Note: we don't increment n here and record in the environment,
                    %% because we need to let the top-level unit id iterate through
                    %% the entire cartesian product of choices.
                    %% Depending on choices made at that leve, the next selection 
                    %% for this prism could be n, n+1, or 0.
                    return choice);
     
     % print (";;; Choice for " ^ anyToString choice.uid ^ " = " ^ anyToString choice.prism_tm ^ "\n");
     % print (";;;  n = " ^ natToString choice.n ^ " of " ^ (natToString (cardinality choice)) ^ "\n");
     applySpecPrismSubstitutionNth prsm choice.n spc pos
    }

  def applySpecPrismSubstitutionNth p n spc pos =
    let sm = p.sms @ n in
    let vinfo = (Morph sm, 0, []) in % TODO: track dependencies better
    let sm_tm = (Quote vinfo, pos) in  % TODO: should sm_tm show the selection from prism?
    auxApplySpecMorphismSubstitution sm spc sm_tm pos 

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%% Subsitute using various sm's on a per-instance basis.
  %%% This is still being developed, and is somewhat problematic.
  %%% For example, should all the ops created by all the sm translations be
  %%% included in the resulting spec, if by chance they are never referenced?
  %%% And what happens when multiple sms interfere with each other via name 
  %%% collisions?
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  applySpecPrismSubstitutionPerInstance : SpecPrism -> Spec -> Position -> Env Spec
(*
  %% TODO: revise to track new spec structure -- needs thought

  def applySpecPrismSubstitutionPerInstance (p as {dom, sms, pmode, tm}) spc pos =
    % let n = random (length sms) in
    % let sm = sms @ n in
    let 

      def translate_op_names op_names =
	foldl (fn (new_names, qid) ->
	       let qid_translations =
	           foldl (fn (names,sm) ->
			  let op_map = opMap sm in
			  case evalPartial op_map qid of
			    | Some qid -> cons (qid, names)
			    | _ -> names)
                         []
			 sms
	       in
		 case qid_translations of
		   | [] -> cons(qid, new_names)
		   | _ -> qid_translations ++ new_names)
              [] 
	      op_names
		 
      def translate_sort_names sort_names =
	foldl (fn (new_names, qid) ->
	       let qid_translations =
	           foldl (fn (names, sm) ->
			  let sort_map = sortMap sm in
			  case evalPartial sort_map qid of
			    | Some qid -> cons (qid, names)
			    | _ -> names)
                         []
			 sms
	       in
		 case qid_translations of
		   | [] -> cons(qid, new_names)
		   | _ -> qid_translations ++ new_names)
              [] 
	      sort_names
		 

    in
    %% Warning: this assumes that dom_spec is a subspec of spc
    %%    S' = M(S - dom(M)) U cod(M)
    let cod_specs = map SpecCalc.cod sms   in  % cod(sm) for each sm
    %% S - dom(P)
    let residue   = subtractSpec spc dom   in  
    let base_spec = getBaseSpec() in
    let cod_tms   = map (fn sm ->
			 case sm.sm_tm of
			   | Some (SpecMorph (_, cod_spec_tm, _), _) -> cod_spec_tm)
                        sms
    in
    let imports   = ListPair.map (fn (x, y) -> (x, y)) (cod_tms, cod_specs) in
    let cod_import_info = {imports         = imports,
			   localOps        = translate_op_names   spc.importInfo.localOps,  
			   localSorts      = translate_sort_names spc.importInfo.localSorts,
			   localProperties = []}
			  
    in
    let new_local_sorts = translate_sort_names spc.importInfo.localSorts in 
    let new_local_ops   = translate_op_names   spc.importInfo.localOps in
    {
     print ("\n;;; Residue:\n");
     print (printSpecExpanded base_spec emptyMap residue);
     print ("\n");
     translated_residue <- applySpecPrism sms residue pos;     % P(S - dom(P))
     print ("\n;;; Translated Residue:\n");
     print (printSpecExpanded base_spec emptyMap translated_residue);
     print ("\n");

     merged_spec <- foldM (fn merged_spec  -> fn cod_spec ->   % for each sm
			   specUnion [merged_spec, cod_spec])  % P(S - dom(P)) U cod(sm) 
                          translated_residue
			  cod_specs;
     new_spec <- return (setImportInfo (merged_spec,
					{imports         = imports,
					 localOps        = new_local_ops,
					 localSorts      = new_local_sorts, 
					 localProperties = spc.importInfo.localProperties
					}));
     print ("\n;;; About to add coercions for :\n");
     print (printSpecExpanded base_spec emptyMap new_spec);
     print ("\n");
     case addCoercions new_spec of
       | Spec s      -> return s
       | Errors msgs -> raise (TypeCheckErrors msgs)}
*)      

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  applySpecPrism : List Morphism -> Spec -> Position -> Env Spec 
  def applySpecPrism sms spc position =
   %% The opMap and sortMap in sm are PolyMap's  :  dom_qid -> cod_qid
   %% but auxTranslateSpec wants AQualifierMap's :  dom_qid -> (cod_qid, cod_aliases)
   %%  so we first convert formats...
   let tmaps = map (fn sm ->
		    let op_translator   = convertIdMap (opMap sm) in
		    let prop_translator = op_translator           in  % TODO: fix evil hack
		    {ambigs = emptyTranslator,
		     sorts  = convertIdMap (sortMap sm),
		     ops    = op_translator,
		     props  = prop_translator,
		     others = None})
                   sms
   in
     auxPrismTranslateSpec spc tmaps position

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  auxPrismTranslateSpec : Spec -> List Translators -> Position -> SpecCalc.Env Spec
  def auxPrismTranslateSpec spc tmaps position =
    let n = length tmaps in
    %% TODO: need to avoid capture that occurs for "X +-> Y" in "fa (Y) ...X..."
    %% TODO: ?? Change UnQualified to new_q in all qualified names ??
    let

      def translateQualifiedIdToAliases translator (qid as Qualified (q, id)) =
        case findAQualifierMap (translator, q,id) of
          | Some (_,new_aliases) -> new_aliases
          | None -> [qid]
  
      def translateSortInfos old_sorts =
        let 
          def translateSortInfo (q, id, info, sorts) =
	    let Qualified (primary_q, primary_id) = primarySortName info in
	    if ~ (q = primary_q && id = primary_id) then
	      return sorts
	    else if exists? basicSortName? info.names then
	      return (insertAQualifierMap (sorts, q, id, info))
	    else
	      {
	       new_names <- foldM (fn new_qids -> fn qid ->
				   foldM (fn new_qids -> fn new_qid ->
					  if new_qid in? new_qids then
					    return new_qids
					  else 
					    return (Cons (new_qid, new_qids)))
				         new_qids
					 (let k = random n in
					  let translators = tmaps @ k in
					  let sort_translator = translators.sorts in
					  translateQualifiedIdToAliases sort_translator qid))
	                          [] 
				  info.names;
	       new_names <- return (reverse new_names);
	       mapM (fn new_qid ->
		     if basicSortName? new_qid then
		       {
			raise_later (TranslationError ("Illegal to translate into base type " ^ (explicitPrintQualifiedId new_qid),
						       position));
			return new_qid
		       }
		     else
		       return new_qid)
	            new_names;
	       return (if unqualified_Boolean in? new_names || Boolean_Boolean in? new_names then
			  sorts
		       else
			 mergeSortInfo spc sorts (info << {names = new_names}))
	      }
	in
	  foldOverQualifierMap translateSortInfo emptyAQualifierMap old_sorts 

      def translateOpInfos old_ops =
        let 
          def translateOpInfo (q, id, info, ops) =
	    let primary_qid as Qualified (primary_q, primary_id) = primaryOpName info in
	    if ~ (q = primary_q && id = primary_id) then
	      return ops
	    else if exists? basicOpName? info.names then
	      return (insertAQualifierMap (ops, q, id, info))
	    else
	      let k = random n in
	      let translators = tmaps @ k in
	      let sort_translator = translators.sorts in
	      let op_translator   = translators.ops   in
	      {
	       new_names <- foldM (fn new_qids -> fn qid ->
				   foldM (fn new_qids -> fn new_qid ->
					  if new_qid in? new_qids then
					    return new_qids
					  else 
					    return (Cons (new_qid, new_qids)))
				         new_qids
					 (translateQualifiedIdToAliases op_translator qid))
	                          [] 
				  info.names;
	       new_names <- return (reverse new_names);
	       mapM (fn new_qid ->
		     if basicOpName? new_qid then
		       {
			raise_later (TranslationError ("Illegal to translate into base op " ^ (explicitPrintQualifiedId new_qid),
						       position));
			return new_qid
		       }
		     else
		       return new_qid)
	            new_names;
	       let (tvs, srt, tm) = unpackFirstOpDef info in
	       let new_srt        = mapSort (translateOpRef   op_translator, 
					     translateSortRef sort_translator, 
					     fn x -> x) 
	                                    srt             
	       in
	       let new_dfn        = maybePiTerm (tvs, SortedTerm (tm, new_srt, termAnn info.dfn)) in
	       let new_info       = info << {names = new_names, 
					     dfn   = new_dfn}      
	       in
	       return (mergeOpInfo spc ops new_info)
	      }
	in
	  foldOverQualifierMap translateOpInfo emptyAQualifierMap old_ops 

     def prismMapSpec tmaps spc =
       spc << {
	       sorts    = prismMapSpecSorts    tmaps spc.sorts,
	       ops      = prismMapSpecOps      tmaps spc.ops,
	       elements = prismMapSpecElements tmaps spc.elements
	      }

     def translatePattern pat = pat
     def translateSortId  srt = srt

     def prismMapSpecSorts tmaps sorts =
       mapSortInfos (fn info -> 
		     let k = random n in
		     let translators = tmaps @ k in
		     let sort_translator = translators.sorts in
		     let op_translator   = translators.ops   in
		     let tsp = (translateOpRef op_translator, translateSortRef sort_translator, translatePattern) in
		     info << {dfn = mapSort tsp info.dfn})
                    sorts
		    
     def prismMapSpecOps tmaps ops =
       mapOpInfos (fn info -> 
		   %% translate sort uniformly, but translate def with variance
		   %% let (tvs, srt, tm) = unpackFirstOpDef info in
		   %% let k = random n in
		   let tsp = (prismTranslateOp tmaps, translateSortId, translatePattern) in
		   info << {dfn = mapTerm tsp info.dfn})
                  ops

     def prismTranslateOp tmaps op_term =
       let k = random n in
       let translators = tmaps @ k in
       let sort_translator = translators.sorts in
       let op_translator   = translators.ops   in
       %% translate op ref and sort associated with it uniformly
       case op_term of
	 | Fun (Op (qid, fixity), srt, pos) ->
	   (let new_qid = translateQualifiedId op_translator qid in
	    let tsp = (prismTranslateOp tmaps, translateSortRef sort_translator, translatePattern) in
	    let new_srt = mapSort tsp srt in
	    if new_qid = qid && equalType?(new_srt, srt) then 
	      op_term 
	    else 
	      Fun (Op (new_qid, fixity), new_srt, pos))
	 | Var ((id,srt),p) ->
	   let new_srt = freshMetaTyVar ("prism", p) in
	   % let _ = toScreen ("\nVar: " ^ (anyToString id) ^ " : " ^ (anyToString srt) ^ " => " ^ (anyToString new_srt) ^ "\n") in
	   Var ((id,new_srt),p)
	 | _ -> op_term

     def prismMapSpecElements tmaps elements =
       map (fn element ->
	    case element of
	      | Property (pt, nm, tvs, term, pos) -> 
		let translators = tmaps @ 0 in
		let sort_translator = translators.sorts in
		let op_translator   = translators.ops   in
		let tsp = (translateOpRef op_translator, translateSortRef sort_translator, translatePattern) in
		Property (pt, nm, tvs, mapTerm tsp term, pos)
	      | _ -> element)
           elements

    in
      let s = prismMapSpec tmaps spc in
      {
       new_sorts <- translateSortInfos s.sorts;
       new_ops   <- translateOpInfos   s.ops;
       return (s << {sorts    = new_sorts,
		     ops      = new_ops})
      }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

}
