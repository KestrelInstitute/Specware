\subsection{Name Qualifing in Specs}

\begin{spec}
SpecCalc qualifying spec 
{
  import Signature 
  import Spec/CompressSpec
  import Spec/MergeSpecs
\end{spec}

To qualify a spec means to change all unqualified names to qualified
names. This can raise exceptions since qualifying a name may identify
it with a name that already exists.

The current version need not visit the imported specs as the hierarchy
is flattened,

Change UnQualified to new_qualifier in all qualified names

\begin{spec} 
  def SpecCalc.evaluateQualify sc_term new_q = 
   let pos = positionOf sc_term in
   {
    value_info as (value,timeStamp,depUnitIds) <- SpecCalc.evaluateTermInfo sc_term;
    case coerceToSpec value of
      | Spec spc -> 
        {
	 qualified_spec <- qualifySpec spc new_q pos;
	 compressed_spec <- complainIfAmbiguous (compressDefs qualified_spec) pos;
	 return (Spec compressed_spec,timeStamp,depUnitIds)
	}
      | Other other -> 
	evaluateOtherQualify sc_term value_info new_q pos
      | _ -> raise (TypeCheck (pos, "qualifying a term that is not a specification"))
   }

  op qualifySpec : Spec -> Qualifier -> Position -> SpecCalc.Env Spec
  def qualifySpec spc new_q position =
    let
      def translateQualifiedId (qid as Qualified (q, id)) =
        if q = UnQualified then
          Qualified (new_q, id)
        else 
          qid
  
      def translateOp op_term =
        case op_term of
         | Fun (Op (qid, fixity), srt, a) ->
           let new_qid = translateQualifiedId qid in
           if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
         | _ -> op_term
  
      def translateSort sort_term =
        case sort_term of
         | Base (qid, srts, a) ->
           let new_qid = translateQualifiedId qid in
           if new_qid = qid then sort_term else Base (new_qid, srts, a)
         | _ -> sort_term
  
      def translatePattern pat = pat
  
      def convertOpMap opMap =
        let def qualifyStep (q, id, info, new_map) =
          %% Translation can cause names to become duplicated, so remove duplicates
	  let new_names = rev (removeDuplicates (map translateQualifiedId info.names)) in
          let new_info = info << {names = new_names} in
          let new_q = if q = UnQualified then new_q else q in
          let old_info = findAQualifierMap (new_map, new_q, id) in 
	  {
	   new_info <- mergeOpInfo spc new_info old_info position;
	   %% Possibly the new name already is used
	   return (insertAQualifierMap (new_map, new_q, id, new_info))
	  } 
	in
        foldOverQualifierMap qualifyStep emptyAQualifierMap opMap 
  
      def convertSortMap sortMap =
        let def qualifyStep (q, id, info, new_map) =
          %% Translation can cause names to become duplicated, so remove duplicates
	  let new_names = rev (removeDuplicates (map translateQualifiedId info.names)) in
          let new_info = info << {names = new_names} in
          let new_q = if q = UnQualified then new_q else q in
          let old_info = findAQualifierMap (new_map, new_q, id) in 
	  {
	   new_info <- mergeSortInfo spc new_info old_info position; 
	   %% Possibly the new name already is used
	   return (insertAQualifierMap (new_map, new_q, id, new_info))
	  } 
	in
	  foldOverQualifierMap qualifyStep emptyAQualifierMap sortMap
  
      def convertProperties properties =
        let def qualifyStep (pt, qid, tvs, fmla) =
          %% Translation can cause names to become duplicated, but won't remove duplicates
          let new_name = translateQualifiedId qid in
          let newProp = (pt, new_name, tvs, fmla) in
	  newProp 
	in
	  List.map qualifyStep properties

      def convertSpec sp =
       let {importInfo = {imports,localOps,localSorts,localProperties}, sorts, ops, properties}
           = mapSpec (translateOp, translateSort, translatePattern) sp
       in 
       {
	newSorts      <- convertSortMap sorts;
	newOps        <- convertOpMap   ops;
	newProperties <- return (convertProperties properties);
	return {importInfo = {imports         = imports,
			      localOps        = map translateQualifiedId localOps,
			      localSorts      = map translateQualifiedId localSorts,
			      localProperties = map translateQualifiedId localProperties},  
		sorts      = newSorts,
		ops        = newOps,
		properties = newProperties}
       }
    in 
      convertSpec spc
}
\end{spec}
