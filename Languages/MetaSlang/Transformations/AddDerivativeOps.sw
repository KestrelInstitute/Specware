(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


AddDerivativeOps qualifying spec

 import /Languages/SpecCalculus/Semantics/Evaluate/Spec
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
 import /Library/Unvetted/Random

 % type MSRules = List MSRule

 type Augmentation  a = OpInfo * OpInfo * a
 type Augmentations a = List (Augmentation a)

 type Context a = {revise_op  : Spec -> OpInfo -> Augmentations a,
                   revise_app : Spec -> OpInfo -> Augmentations a -> MSTerm -> Option MSTerm}

 op infoName (info : OpInfo) : String = 
  printQualifiedId (head info.names)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% create new versions of ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [a] defineDerivativeOps (context : Context a)
                            (spc     : Spec) 
  : SpecCalc.Env (Spec * Augmentations a) =
  let augmentations =
      foldOpInfos (fn (info, augmentations) -> 
                     case context.revise_op spc info of
                       | [] -> augmentations
                       | new_augs -> 
                         %% let _ = writeLine ("From " ^ infoName info ^ " adding " ^ anyToString (length new_augs) ^ " new ops") in
                         augmentations ++ new_augs)
                  []
                  spc.ops
  in
  let new_infos = map (fn (_, new_info, _) -> new_info) augmentations in
  let _ = map (fn (_, new_info, revision) ->
                 writeLine ("Adding " ^ infoName new_info ^ " with revision " ^ anyToString revision))
              augmentations
  in
  {
   new_spec <- addOps (spc, new_infos);
   return (new_spec, augmentations)
   }

 op addOps (spc : Spec, new_infos : List OpInfo) : SpecCalc.Env Spec =
  foldM (fn spc -> fn new_info ->
           addOp new_info.names new_info.fixity false new_info.dfn spc noPos)
        spc
        new_infos

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% revise calls to use new versions of ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [a] replaceCallsInInfo (context       : Context a) 
                           (augmentations : Augmentations a) 
                           (spc           : Spec)
                           (info          : OpInfo)
  : SpecCalc.Env Spec =
  %% let _ = writeLine ("--- " ^ infoName info) in
  let
    def revise_apply (tm : MSTerm) : MSTerm =
      case tm of
        | Apply (Fun (Op (qid, _), typ, _), Record (fields, _), _) -> 
          (case context.revise_app spc info augmentations tm of
             | Some new_tm -> new_tm
             | _ -> tm)
        | _ -> tm

    def maybe_revise_dfn info =
      let dfn = firstOpDef info in
      let new_dfn = mapTerm (revise_apply, fn typ -> typ, fn pat -> pat) dfn in
      if equalTerm? (dfn, new_dfn) then
        None
      else
        Some new_dfn
  in
  case maybe_revise_dfn info of
    | Some new_dfn -> 
      %% addOrRefineOp: QualifiedIds -> Fixity -> Bool -> MSTerm -> Spec -> Position -> 
      %%                Option SpecElement -> Bool -> SpecCalc.Env(Spec * SpecElement)
      %% def addOrRefineOp new_names new_fixity refine? new_dfn old_spec pos opt_next_el addOnly? =
      %% let _ = writeLine("Changed a call in " ^ infoName info) in
      {(spc, _) <- addOrRefineOp info.names info.fixity true new_dfn spc noPos None true;
       return spc}
    | _ -> 
      %% let _ = writeLine("No changes in " ^ infoName info) in
      return spc

 op [a] replaceCallsInSpec (context       : Context a)
                           (spc           : Spec) 
                           (augmentations : Augmentations a)
  : SpecCalc.Env Spec =
  let infos = foldOpInfos (fn (info, infos) -> info :: infos) [] spc.ops in
  foldM (replaceCallsInInfo context augmentations) spc infos

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% add new versions of ops and revise calls to use them
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op [a] addDerivativeOps (context : Context a) (spc : Spec) : SpecCalc.Env Spec =
  {
   (spec_with_new_ops, augmentations) <- defineDerivativeOps context spc;
   replaceCallsInSpec context spec_with_new_ops augmentations 
   }

end-spec

