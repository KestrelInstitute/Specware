% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUnion.sl, v1.3

SpecUnion qualifying spec 
 import ../Environment  % foldM    
 import /Languages/MetaSlang/Specs/StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities
 import Spec/MergeSpecs
 import Spec/CompressSpec

 op specUnion  : List Spec            -> Env Spec
 op sortsUnion : List Spec            -> Env SortMap
 op opsUnion   : List Spec -> SortMap -> Env OpMap
 op eltsUnion  : List Spec            -> Env SpecElements

 %% specUnion is called by specColimit to create apex spec, 
 %% and also by applySpecMorphismSubstitution to stich together 
 %% the translated and non-translated portions of the subject spec.

 def specUnion specs =
%  let merged_imports     = importsUnion    specs in
%  %% let merged_local_ops   = localOpsUnion   specs in
%  %% let merged_local_sorts = localSortsUnion specs in
%  let merged_local_sorts = foldl (fn (spc, names) -> names ++ spc.importInfo.localSorts)      [] specs in
%  let merged_local_ops   = foldl (fn (spc, names) -> names ++ spc.importInfo.localOps)        [] specs in
%  let merged_local_elts = foldl (fn (spc, names) -> names ++ spc.importInfo.localProperties) [] specs in
%  let merged_import_info = {imports         = merged_imports,
%			    localOps        = merged_local_ops,
%			    localSorts      = merged_local_sorts,
%			    localProperties = merged_local_elts} 
%  in
  {
   merged_sorts <- sortsUnion specs;
   merged_ops   <- opsUnion   specs merged_sorts;
   merged_elts  <- eltsUnion specs;
   merged_spec  <- return {sorts      = merged_sorts,
			   ops        = merged_ops,
			   elements   = merged_elts,
			   qualified? = false};
   return (compressDefs (removeDuplicateImports merged_spec))
  }

 %% TODO: The terms for the imports might not remain in a meaningful URI context -- relativize to new context
% def importsUnion specs =
%  foldl (fn (spc, imports) -> listUnion (spc.importInfo.imports, imports))
%        []
%        specs

%%% def localSortsUnion specs =
%%%  foldl (fn (spc, local_sorts) -> listUnion (spc.importInfo.localSorts, local_sorts))
%%%        []
%%%        specs
%%%
%%% def localOpsUnion specs =
%%%  foldl (fn (spc, local_ops) -> listUnion (spc.importInfo.localOps, local_ops))
%%%        []
%%%        specs

 def sortsUnion specs =
  let ops = (hd specs).ops in
  foldM (fn combined_sorts -> fn next_spec -> 
	 unionSortMaps combined_sorts next_spec.sorts ops)
        emptySortMap 
	specs

 def opsUnion specs sorts = 
  foldM (fn combined_ops -> fn next_spec -> 
	 unionOpMaps combined_ops next_spec.ops sorts)
        emptyOpMap
	specs

 def eltsUnion specs =
  foldM (fn combined_elts -> fn next_spec -> 
	 unionElts combined_elts next_spec.elements)
        [] % emptyElts
	specs
 
 def unionSortMaps old_sorts new_sorts ops =
   %% Jan 8, 2003: Fix for bug 23
   %% Assertion: If new_sorts at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   let 
      def augmentSortMap (q, id, info, sorts) =
        let Qualified (primary_q, primary_id) = primarySortName info in
        if q = primary_q & id = primary_id then
          %% Assertion: We take this branch exactly once per new info.
	  mergeSortInfo sorts ops info noPos
        else
	  return sorts
   in
    foldOverQualifierMap augmentSortMap old_sorts new_sorts

 def unionOpMaps old_ops new_ops sorts =
   %% Jan 8, 2003: Fix for bug 23
   %% Assertion: If new_op_map at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   let 
      def augmentOpMap (q, id, info, ops) =
        let Qualified (primary_q, primary_id) = primaryOpName info in
        if q = primary_q & id = primary_id then
          %% Assertion: We take this branch exactly once per new info.
	  mergeOpInfo sorts ops info noPos
	else
	  return ops
   in
    foldOverQualifierMap augmentOpMap old_ops new_ops

 def unionElts old_elts new_elts =
   %% TODO:  These might refer incorrectly into old specs
   %% TODO:  listUnion assumes = test on elements, we might want something smarter such as equivTerm?
   %% TODO: This might be very inefficient
   return (listUnion (old_elts, new_elts))

endspec
