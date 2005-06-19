% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUnion.sl, v1.3

SpecUnion qualifying spec 

 import ../Environment  % foldM    
 import /Languages/MetaSlang/Specs/StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities
 import Spec/MergeSpecs
 import Spec/VarOpCapture
 import Spec/CompressSpec

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyElements : SpecElements = []

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% specUnion is called by specColimit to create apex spec, 
 %% and also by applySpecMorphismSubstitution to stich together 
 %% the translated and non-translated portions of the subject spec.

 op  specUnion : List Spec -> Position -> Env Spec
 def specUnion specs pos =
  {
   new_spec  <- return (auxSpecUnion specs);
   new_spec  <- complainIfAmbiguous new_spec pos;
   raise_any_pending_exceptions;
   return new_spec
  }

 op  auxSpecUnion : List Spec -> Spec
 def auxSpecUnion specs =
   let new_spec = {sorts      = sortsUnion specs,
		   ops        = opsUnion   specs,
		   elements   = eltsUnion  specs,
		   qualified? = false}
   in
   let new_spec = removeDuplicateImports new_spec in
   let new_spec = removeVarOpCaptures    new_spec in
   let new_spec = compressDefs           new_spec in
   new_spec

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op sortsUnion : List Spec -> SortMap
 op opsUnion   : List Spec -> OpMap
 op eltsUnion  : List Spec -> SpecElements

 def sortsUnion specs = foldl unionSortMaps emptySortMap  specs
 def opsUnion   specs = foldl unionOpMaps   emptyOpMap    specs
 def eltsUnion  specs = foldl unionElts     emptyElements specs
 
 def unionSortMaps (next_spec, sorts) =
   %% Jan 8, 2003: Fix for bug 23
   %% Assertion: If new_sorts at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   foldriAQualifierMap (fn (q, id, info, sorts) ->
			let Qualified (primary_q, primary_id) = primarySortName info in
			if q = primary_q & id = primary_id then
			  %% Assertion: We take this branch exactly once per new info.
			  mergeSortInfo sorts info % may introduce duplicate defs
			else
			  sorts)
                       sorts 
		       next_spec.sorts

 def unionOpMaps (next_spec, ops) =
   %% Assertion: If new_op_map at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   foldriAQualifierMap (fn (q, id, info, ops) ->
			let Qualified (primary_q, primary_id) = primaryOpName info in
			if q = primary_q & id = primary_id then
			  %% Assertion: We take this branch exactly once per new info.
			  mergeOpInfo ops info % may introduce duplicate defs
			else
			  ops)
                       ops 
		       next_spec.ops

 def unionElts (next_spec, elts) =
   %% TODO:  These might refer incorrectly into old specs
   %% TODO:  listUnion assumes = test on elements, we might want something smarter such as equivTerm?
   %% TODO: This might be very inefficient
   listUnion (elts, next_spec.elements)

endspec
