(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUnion.sl, v1.3

SpecUnion qualifying spec 

 import /Languages/SpecCalculus/Semantics/Environment % foldM    
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm % SCTerm

 import /Library/Legacy/DataStructures/ListUtilities

 import /Languages/MetaSlang/Specs/StandardSpec
 import /Languages/MetaSlang/Specs/CompressSpec

 import Spec/MergeSpecs
 import Spec/VarOpCapture
 import Spec/ComplainIfAmbiguous

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyElements : SpecElements = []

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% specUnion is called by specColimit to create apex spec, 
 %% and also by applySpecMorphismSubstitution to stich together 
 %% the translated and non-translated portions of the subject spec.

 op  specUnion : Specs -> Position -> Env Spec
 def specUnion specs pos =
  {
   new_spec  <- return (auxSpecUnion specs);
   new_spec  <- complainIfAmbiguous new_spec pos;
   raise_any_pending_exceptions;
   return new_spec
  }

 op  auxSpecUnion : Specs -> Spec
 def auxSpecUnion specs =
   let new_spec = emptySpec << {types     = typesUnion specs,
                                ops       = opsUnion   specs,
                                elements  = eltsUnion  specs,
                                qualifier = None}
   in
   let new_spec = removeDuplicateImports new_spec in
   let new_spec = removeVarOpCaptures    new_spec in
   % let new_spec = compressDefs           new_spec in
   new_spec

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op typesUnion : Specs -> TypeMap
 op opsUnion   : Specs -> OpMap
 op eltsUnion  : Specs -> SpecElements

 def typesUnion specs = foldl unionTypeMaps emptyTypeMap  specs
 def opsUnion   specs = foldl unionOpMaps   emptyOpMap    specs
 def eltsUnion  specs = foldl unionElts     emptyElements specs
 
 def unionTypeMaps (types, next_spec) =
   %% Jan 8, 2003: Fix for bug 23
   %% Assertion: If new_types at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   foldriAQualifierMap (fn (q, id, info, types) ->
			let Qualified (primary_q, primary_id) = primaryTypeName info in
			if q = primary_q && id = primary_id then
			  %% Assertion: We take this branch exactly once per new info.
			  mergeTypeInfo next_spec types info % may introduce duplicate defs
			else
			  types)
                       types 
		       next_spec.types

 def unionOpMaps (ops, next_spec) =
   %% Assertion: If new_op_map at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   foldriAQualifierMap (fn (q, id, info, ops) ->
			let Qualified (primary_q, primary_id) = primaryOpName info in
			if q = primary_q && id = primary_id then
			  %% Assertion: We take this branch exactly once per new info.
			  mergeOpInfo next_spec ops info true % may introduce duplicate defs
			else
			  ops)
                       ops 
		       next_spec.ops

 def unionElts (elts, next_spec) =
   %% TODO:  These might refer incorrectly into old specs
   %% TODO:  listUnion assumes = test on elements, we might want something smarter such as equivTerm?
   %% TODO: This might be very inefficient
   listUnion (elts, next_spec.elements)

endspec
