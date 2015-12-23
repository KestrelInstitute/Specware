(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CGen qualifying spec

% import /Languages/MetaSlang/CodeGen/C/SpecToCSpec
import /Languages/MetaSlang/Transformations/Pragma

import /Languages/MetaSlang/CodeGen/Generic/SliceSpec

op builtinCOp? (Qualified (q, id) : QualifiedId) : Bool =
 case q of
   | "Bool"       -> id in? ["true", "false", "~", "&&", "||", "=>", "<=>", "~="]
   | "Integer"    -> id in? ["zero", "isucc", "ipred", "one", "+", "-", "*", "<", ">", "<=", ">=", "natMinus"]
   | "IntegerAux" -> id in? ["-"]  % unary minus
   | "Nat"        -> id in? ["succ", "pred", "+", "*"]
   | "Char"       -> id in? []
   | "String"     -> id in? ["^"]
   | "System"     -> id in? ["writeLine", "toScreen", "setf"]
   | "Function"   -> id in? []
   | "List"       -> id in? []
   | "Handcoded"  -> true
   | _ -> false

op builtinCType? (Qualified (q, id) : QualifiedId) : Bool =
 case q of
   | "Bool"          -> id in? ["Bool"]
   | "Integer"       -> id in? ["Int8", "Int16", "Int32"] 
   | "Int"           -> id in? ["Int8", "Int16", "Int32"]
   | "Nat"           -> id in? ["Nat8", "Nat16", "Nat32"]
   | "Char"          -> id in? ["Char"]
   | "String"        -> id in? ["String"]
   | "List"          -> id in? []
   | "<unqualified>" -> id in? ["Ptr"]
   | _ -> false
      
%% TODO: for now, transform is just for debugging
op SpecTransform.sliceSpecForC (ms_spec    : Spec)
                               (msg        : String)
                               (root_ops   : QualifiedIds)
                               (root_types : QualifiedIds)
 : Spec =
 SpecTransform.newSliceSpecForC ms_spec msg root_ops root_types

%% TODO: deprecate this for name above
op SpecTransform.newSliceSpecForC (ms_spec    : Spec)
                                  (msg        : String)
                                  (root_ops   : QualifiedIds)
                                  (root_types : QualifiedIds)
 : Spec =
 let slice = sliceForCGen (ms_spec, root_ops, root_types) in
 let _     = describeSlice ("For C: " ^ msg, slice) in
 ms_spec
 
op defaultSliceForCGen (ms_spec : Spec) : Slice =
 let root_ops   = topLevelOpNames   ms_spec in
 let root_types = topLevelTypeNames ms_spec in
 sliceForCGen (ms_spec, root_ops, root_types)
 
%% TODO: This will be used by other transforms
op sliceForCGen (ms_spec    : Spec,
                 root_ops   : QualifiedIds,
                 root_types : QualifiedIds)
 : Slice =
 let
   def c_oracle (pending_ref, slice) =
     case pending_ref of
       | Op pending_op_ref ->
         let name = pending_op_ref.name in
         if builtinCOp? name then
           Some Primitive
         else if name in? slice.lm_data.native_ops then
           Some API
         else if name in? slice.lm_data.op_macros then
           Some Macro
         else
           None
       | Type pending_type_ref ->
         let name = pending_type_ref.name in
         if builtinCType? name then
           Some Primitive
         else if name in? slice.lm_data.native_types then
           Some API
         else if name in? slice.lm_data.type_macros then
           Some Macro
         else
           None
       | Theorem pending_tref ->
         None
 in
 executionSlice (ms_spec, parseCTranslationPragmas, c_oracle, root_ops, root_types)

op parseCTranslationPragmas (s : Spec) : LanguageMorphisms =
 parseTranslationPragmas "C" s 

end-spec
