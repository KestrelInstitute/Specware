SpecCalc qualifying spec 

  import Signature 
  import Spec/MergeSpecs
  import Spec/VarOpCapture
  import Spec/CompressSpec

  %% To qualify a spec means to change all unqualified names to qualified
  %% names. This can raise exceptions since qualifying a name may identify
  %% it with a name that already exists.
  %% 
  %% The current version need not visit the imported specs as the hierarchy
  %% is flattened,
  %% 
  %% Change UnQualified to new_qualifier in all qualified names

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def SpecCalc.evaluateQualify sc_term new_q = 
   let pos = positionOf sc_term in
   {
    value_info as (value, ts, uids) <- SpecCalc.evaluateTermInfo sc_term;
    case coerceToSpec value of
      | Spec spc -> 
        {
	 qualified_spec <- qualifySpec spc new_q [] pos;
	 return (Spec qualified_spec, ts, uids)
	}
      | Other other -> 
	evaluateOtherQualify sc_term value_info new_q pos
      | _ -> raise (TypeCheck (pos, "qualifying a term that is not a specification"))
   }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% qualifySpec is also called from Accord
  op  qualifySpec : Spec -> Qualifier -> Ids -> Position -> SpecCalc.Env Spec
  def qualifySpec spc new_q immune_ids pos =

    %% For core Specware per se, immune_ids will be [].
    %% But in some contexts (e.g. Accord) we might have "local" ops that 
    %% we would prefer not to qualify.  
    %% Moreover, by definition only unqualified names are candidates for 
    %% qualification, so we need only check the ids of the "local" ops
    %% (as opposed to checking against the full name).

    let

      def qualify_sort sort_term =
        case sort_term of
         | Base (qid, srts, a) ->
           let new_qid = qualifySortId new_q qid in
           if new_qid = qid then sort_term else Base (new_qid, srts, a)
         | _ -> sort_term
  
      def qualify_term op_term =
        case op_term of
         | Fun (Op (qid, fixity), srt, a) ->
           let new_qid = qualifyOpId new_q immune_ids qid in
           if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
         | _ -> op_term
  
      def qualify_pattern pat = pat
  
      def qualify_sorts sorts =
        let 
          def qualify_sortinfo (q, _, info, sorts) =
	    let revised_q = if q = UnQualified then new_q else q in
	    %% Translation can cause names to become duplicated, so remove duplicates
	    let new_names = rev (removeDuplicates (map (qualifySortId revised_q) info.names)) in % revised_q was new_q ??
	    let new_info  = info << {names = new_names} in
	    return (mergeSortInfo spc sorts new_info)
	in
	  foldOverQualifierMap qualify_sortinfo emptyAQualifierMap sorts

      def qualify_ops ops =
        let 
          def qualify_opinfo (q, id, info, ops) =
	    let revised_q = if q = UnQualified && ~ (member (id, immune_ids)) then new_q else q in
	    %% Translation can cause names to become duplicated, so remove duplicates
	    let new_names = rev (removeDuplicates (List.map (qualifyOpId revised_q immune_ids) info.names)) in % revised_q was new_q ??
	    let new_info  = info << {names = new_names} in
	    return (mergeOpInfo spc ops new_info)
	in
	  foldOverQualifierMap qualify_opinfo emptyAQualifierMap ops 
  
    in
    let {sorts, ops, elements, qualified?} = 
        mapSpecUnqualified (qualify_term, qualify_sort, qualify_pattern) spc
    in 
    {
     newSorts    <- qualify_sorts sorts;
     newOps      <- qualify_ops   ops;
     newElements <- return (qualifySpecElements new_q immune_ids elements);
     new_spec    <- return {sorts      = newSorts,
			    ops        = newOps,
			    elements   = newElements,
			    qualified? = true};
     new_spec    <- return (removeVarOpCaptures new_spec);
     new_spec    <- return (compressDefs        new_spec);
     new_spec    <- complainIfAmbiguous new_spec pos;
     raise_any_pending_exceptions;
     return new_spec
    }
      
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% Accord prefers to have qualifySpecElements and qualifySpecElement
  %% as standalone functions (not local to qualifySpec) so it can call 
  %% them from other contexts, as when qualifying modules, classes, etc.

  op  qualifySpecElements : Qualifier -> Ids -> SpecElements -> SpecElements
  def qualifySpecElements new_q immune_ids elts =
    List.map (qualifySpecElement new_q immune_ids) elts

  op  qualifySpecElement : Qualifier -> Ids -> SpecElement -> SpecElement
  def qualifySpecElement new_q immune_ids el =
    case el of
      | Import (sp_tm, sp, els) ->
        if qualifiedSpec? sp then 
	  el
	else 
	  Import ((Qualify (sp_tm, new_q), noPos),
		  sp,
		  qualifySpecElements new_q immune_ids els)
      | Op      qid -> Op      (qualifyOpId   new_q immune_ids qid)
      | OpDef   qid -> OpDef   (qualifyOpId   new_q immune_ids qid)
      | Sort    qid -> Sort    (qualifySortId new_q qid)
      | SortDef qid -> SortDef (qualifySortId new_q qid)
      | Property(pt, qid, tvs, fmla) ->
	%% Translation can cause names to become duplicated, but won't remove duplicates
	let new_name = qualifyPropertyId new_q qid in
	let newProp = (pt, new_name, tvs, fmla) in
	Property newProp
      | _ -> el

  def qualifyOpId new_q immune_ids (qid as Qualified (q, id)) =
    if q = UnQualified && ~ (member (id, immune_ids)) then
      Qualified (new_q, id)
    else 
      qid

  def qualifySortId new_q (qid as Qualified (q, id)) =
    if q = UnQualified then
      Qualified (new_q, id)
    else 
      qid

  def qualifyPropertyId new_q (qid as Qualified (q, id)) =
    if q = UnQualified then
      Qualified (new_q, id)
    else 
      qid
  
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
