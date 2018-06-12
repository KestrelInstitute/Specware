(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec

import ../../Environment
import /Languages/MetaSlang/Specs/Equivalences
import /Languages/MetaSlang/Specs/Utilities
import /Library/Structures/Data/Sets/AsSTHarray


op [a] compatibleTypes1? (ty1: AType a, ty2: AType a, ignore_subtypes?: Bool) : Bool =
 anyType? ty1 ||
 anyType? ty2 ||
 equalTypeSubtype? (ty1, ty2, ignore_subtypes?)

op  mergeTypeInfo (_ : Spec) (types : TypeMap) (info : TypeInfo) : TypeMap =
 let
   def aux (new_info, Qualified (q, id)) =
     case findAQualifierMap (types, q, id) of

       | Some old_info ->
         let names                 = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
         let names                 = removeDuplicates     names                 in % redundant?
         let (old_decls, old_defs) = typeInfoDeclsAndDefs old_info              in
         let (new_decls, new_defs) = typeInfoDeclsAndDefs new_info              in
         let combined_decls =
             foldl (fn (combined_decls, new_decl) ->
                      %% For now, use equalType?, as opposed to equivType? --
                      %% will do that compression later in compressDefs when full context is available
                      if exists? (fn old_decl -> equalType? (new_decl, old_decl)) combined_decls then
                        combined_decls
                      else
                        new_decl :: combined_decls)
                   old_decls
                   new_decls
         in
         let combined_defs =
             foldl (fn (combined_defs, new_def) ->
                      %% For now, use equalType?, as opposed to equivType? --
                      %% will do that compression later in compressDefs when full context is available
                      if exists? (fn old_def -> equalType? (new_def, old_def)) combined_defs then
                        combined_defs
                      else
                        new_def :: combined_defs)
                   old_defs
                   new_defs
         in
         %% Defer checks for duplicate definitions until later, after the caller
         %% has had a chance to call compressDefs
         let combined_dfn = maybeAndType (combined_decls ++ combined_defs, typeAnn new_info.dfn) in
         {names = names,
          dfn   = combined_dfn}

       | _ -> new_info
 in
 let merged_info = foldl aux info info.names in
 foldl (fn (types, Qualified (q, id)) ->
          insertAQualifierMap (types, q, id, merged_info))
       types
       merged_info.names  % new and old

op MSPS.debug?: Bool = false

op getFirstFilePosition (tm : MSTerm) : Option Position =
 foldSubTerms (fn (stm, result) ->
                 if some? result then
                   result
                 else
                   let pos = termAnn stm in
                   if embed? File pos then
                     Some pos
                   else
                     None)
              None
              tm

op printOptPosition (o_p : Option Position) : String =
 case o_p of

   | Some (File (filename, left, _)) ->
     "Line " ^ show (left.1 - 1) ^ " of " ^ filename ^ "\n"

   | _ -> ""

op mergeOpInfo (spc: Spec) (ops: OpMap) (info: OpInfo) (ignore_subtypes?: Bool): OpMap =
 let
   def aux (new_info, Qualified (q, id)) =
     case findAQualifierMap (ops, q, id) of

       | Some old_info ->
         if new_info = old_info then
           new_info
         else
           let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
           let combined_names  = removeDuplicates names in % redundant?
           %% defer checks for conflicting fixities until later, after the caller
           %% has had a chance to call compressDefs
           let combined_fixity =
               if new_info.fixity = old_info.fixity then
                 new_info.fixity
               else
                 Error [new_info.fixity, old_info.fixity]
           in
           let old_type_tms = unpackTypedTerms old_info.dfn in
           let new_type_tms = unpackTypedTerms new_info.dfn in
           let (pref_type_tms, non_pref_sub_type_tms) =
               if (length old_type_tms = length new_type_tms && notAnyTermTriple? old_type_tms)
                 || length old_type_tms > length new_type_tms
                 then
                 (old_type_tms, new_type_tms)
               else
                 (new_type_tms, old_type_tms)
           in
           let sub_pref_type_tms = suffix (pref_type_tms, length non_pref_sub_type_tms) in
           % let merge_bad? = exists?(fn ((new_tvs, new_ty, new_dfn),
           %                         (old_tvs, old_ty, old_dfn))
           %                       ->
           %                       ~ (new_tvs = old_tvs
           %                          && compatibleTypes1? (new_ty,  old_ty, ignore_subtypes?)
           %                          && compatibleTerms?  (new_dfn, old_dfn)))
           %                    (zip (sub_pref_type_tms,
           %                          non_pref_sub_type_tms))
           % in
           % let _ = if merge_bad?
           %           then
           %             let o_pos_new = getFirstFilePosition new_info.dfn in
           %             let o_pos_old = getFirstFilePosition  old_info.dfn in
           %             warn ("mergeOpInfo conflict for "^q^"."^id^":\n"
           %                   ^ printTerm new_info.dfn ^ "\n" ^ printOptPosition o_pos_new
           %                   ^ printTerm old_info.dfn ^ "\n" ^ printOptPosition o_pos_old)
           %         else
           %           ()
           % in
           let combined_type_tms =
               prefix (pref_type_tms,
                       length pref_type_tms - length non_pref_sub_type_tms)
               ++
               map (fn ((new_tvs, new_ty, new_dfn),
                        (old_tvs, old_ty, old_dfn))
                      ->
                      if new_tvs = old_tvs
                          && compatibleTypes? (new_ty,  old_ty)
                          && compatibleTerms? (new_dfn, old_dfn)
                        then
                          (new_tvs,
                           chooseDefinedType (old_ty,  new_ty),
                           chooseDefinedTerm (old_dfn, new_dfn))
                      else
                        (new_tvs, new_ty, new_dfn))
                   (zip (sub_pref_type_tms, non_pref_sub_type_tms))
           in
           let combined_dfn = maybePiAndTypedTerm combined_type_tms in
           let _ = if true then   % ~merge_bad?
                     ()
                   else
                     writeLine ("merge old: "   ^ id ^ "\n" ^ printTerm old_info.dfn
                                 ^ "\n with \n" ^ printTerm new_info.dfn
                                 ^ "\n to\n"    ^ printTerm combined_dfn)
           in
           new_info << {names           = combined_names,
                        dfn             = combined_dfn,
                        fullyQualified? = false}

       | _ -> new_info
 in
 let merged_info = foldl aux info info.names in
 foldl (fn (ops, Qualified (q, id)) ->
          insertAQualifierMap (ops, q, id, merged_info))
       ops
       merged_info.names  % new and old

op combineDecls (old_decl : MSTerm,
                 new_decl : MSTerm,
                 old_def  : MSTerm,
                 new_def  : MSTerm)
 : MSTerms =
 case (old_decl, new_decl) of

   | (Pi (o_tvs, old_tm, _),
      Pi (n_tvs, new_tm, a))
     | o_tvs = n_tvs ->
       map (fn t -> Pi (n_tvs, t, a))
           (combineDecls (old_tm, new_tm, old_def, new_def))

   | (TypedTerm (old_stm, old_ty, _),
      TypedTerm (new_stm, new_ty, a2))
     ->
     let comb_ty = combineSubTypes (old_ty, new_ty, old_def, new_def) in
     map (fn comb_tm -> TypedTerm (comb_tm, comb_ty, a2))
         (combineDecls (old_stm, new_stm, old_def, new_def))

   | _ ->
     if equalTerm? (new_decl, old_decl) then
       [new_decl]
     else
       [new_decl, old_decl]

%% Just removes duplicate imports although could also remove other duplicate elements
%% but this would be more expensive and maybe not that helpful
%% Update: In fact, looking for all duplicates seems to take a lot of time.
%%         It added 9(!) minutes to the normal 3 or 4 minutes for processing
%%         all the specs in Specware itself.

op removeDuplicateImports (spc : Spec) : Spec =
 let opt_base_spec = maybeGetBaseSpec () in
 let

   def remove_duplicates (elements, seen, saw_base?) =
     case elements of

       | [] ->
         ([], [], seen, saw_base?)

       | this_element :: tail ->
         case this_element of

           | Import (spec_tm, imported_original_spec, imported_elements, pos) ->

             let importing_base? =
                 case opt_base_spec of
                   | Some base_spec -> imported_original_spec = base_spec
                   | _ -> false
             in
             if importing_base? then

               %% Special processing for base spec, since we see it often.

               if saw_base? then
                 remove_duplicates (tail, seen, true)
               else
                 let (revised_elements_in_tail, non_imports_in_tail, seen, _) =
                     remove_duplicates (tail, seen, true)
                 in
                 let revised_elements = this_element :: revised_elements_in_tail in
                 let non_imports      = non_imports_in_tail                      in
                 (revised_elements,
                  non_imports,
                  seen,
                  true)

             else

               %% If we're importing something other than the base spec, process it and record it as seen.

               %% Each seen entry contains the original spec and top-level non-import elements.
               %% (We deliberately ignore imports within entries.)

               let (revised_elements_in_import, non_imports_in_import, seen, saw_base?) =
                   remove_duplicates (imported_elements, seen, saw_base?)
               in
               let this_entry = (imported_original_spec, non_imports_in_import) in
               if Set.member? seen this_entry then
                 remove_duplicates (tail, seen, saw_base?)
               else
                 let revised_import = Import (spec_tm,
                                              imported_original_spec,
                                              revised_elements_in_import,
                                              pos)
                 in
                 let seen = Set.insert seen this_entry in
                 let (revised_elements_in_tail, non_imports_in_tail, seen, saw_base?) =
                     remove_duplicates (tail, seen, saw_base?)
                 in
                 let revised_elements = revised_import :: revised_elements_in_tail in
                 let non_imports      = non_imports_in_tail                        in
                 (revised_elements,
                  non_imports,
                  seen,
                  saw_base?)

           | _ ->
             %% this_element is not an import: it is a type, op, axiom, pragma, etc.
             let (revised_elements_in_tail, non_imports_in_tail, seen, saw_base?) =
                 remove_duplicates (tail, seen, saw_base?)
             in
             let revised_elements = this_element :: revised_elements_in_tail in
             let non_imports      = this_element :: non_imports_in_tail      in
             (revised_elements,
              non_imports,
              seen,
              saw_base?)
 in
 let (revised_elements, _, _, _) = remove_duplicates (spc.elements, Set.empty, false) in
 spc << {elements = revised_elements}

end-spec
