(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecToLisp qualifying spec

import /Languages/MetaSlang/CodeGen/Generic/SliceSpec

op builtInLispOp?   (qid : QualifiedId) : Bool = 
 printPackageId(qid, "") in? SpecToLisp.SuppressGeneratedDefuns

op builtInLispType? (qid : QualifiedId) : Bool = 
 false

op SpecTransform.sliceSpecForLisp (ms_spec    : Spec)
                                  (root_ops   : QualifiedIds)
                                  (root_types : QualifiedIds)
 : Spec =
 let msg   = "" in
 let slice = sliceForLispGen ms_spec root_ops root_types in
 % let _     = describeSlice ("For Lisp: " ^ msg, slice) in
 ms_spec

op sliceForLispGen (ms_spec    : Spec)
                   (root_ops   : QualifiedIds)
                   (root_types : QualifiedIds)
 : Slice =
 let
   def lisp_oracle (pending_ref, slice) =
     case pending_ref of
       | Op pending_op_ref ->
         let name = pending_op_ref.name in
         if builtInLispOp? name then
           Some Primitive
         else if name in? slice.lm_data.native_ops then
           Some API
         else if name in? slice.lm_data.op_macros then
           Some Macro
         else
           None
       | Type pending_type_ref ->
         let name = pending_type_ref.name in
         if builtInLispType? name then
           Some Primitive
         else if name in? slice.lm_data.native_types then
           Some API
         else if name in? slice.lm_data.type_macros then
           Some Macro
         else
           None
       | Theorem _ ->
         None
 in
 executionSlice (ms_spec, parseLispTranslationPragmas, lisp_oracle, root_ops, root_types)

op parseLispTranslationPragmas (s : Spec) : LanguageMorphisms =
 parseTranslationPragmas "Lisp" s

end-spec
