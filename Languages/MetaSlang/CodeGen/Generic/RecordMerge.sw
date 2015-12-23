(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Transform qualifying spec
 import /Languages/MetaSlang/Specs/Environment

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op SpecTransform.introduceRecordMerges (spc: Spec): Spec =
   mapSpec (makeRecordMerge spc, id, id) spc

 op makeTupleUpdate?: Bool = true

 op makeRecordMerge (spc: Spec) (tm: MSTerm): MSTerm =
   case tm of
     | Record (fields as (id0, _) :: _, _) | (id0 ~= "1" || makeTupleUpdate?) ->
       (case maybeTermType tm of
          | None -> tm
          | Some rec_ty ->
            let (src_tms, new_fields) =
                foldr (fn ((id1, t), (src_tms, new_fields)) ->
                         case t of
                           | Apply (Fun (f, _, _), src_tm, _)
                               | projectionFun(f, spc) = Some id1 && equivTypeSubType? spc (termType src_tm, rec_ty) true 
                             ->
                             (if termIn? (src_tm, src_tms) then 
                                src_tms 
                              else 
                                src_tm :: src_tms,
                              new_fields)
                           | _ -> 
                             (src_tms, 
                              (id1, t) :: new_fields))
                      ([], []) 
                      fields
        in
        (case src_tms of
           | [src_tm] ->
             if new_fields = [] then 
               src_tm
             else 
               mkRecordMerge (src_tm, mkRecord new_fields)
           | _ -> tm))
     | _ -> tm

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op SpecTransform.expandRecordMerges (spc : Spec) : Spec =
   mapSpec (fn tm -> translateRecordMerge spc tm, id, id) spc

 %% translateRecordMerge is used by tryEvalOne in Utilities.sw, otherwise would move it here

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
