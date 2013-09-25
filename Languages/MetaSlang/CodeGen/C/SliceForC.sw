CGen qualifying spec

import /Languages/MetaSlang/CodeGen/C/SpecToCSpec
import /Languages/MetaSlang/Transformations/SliceSpec

op builtinCOp? (Qualified (q, id) : QualifiedId) : Bool =
 % TODO: ugly and a maintenance problem -- rethink
 case q of

   %% Base specs:
   | "Bool"       -> id in? ["true", "false", "~", "&&", "||", "=>", "<=>", "~="]
   | "Integer"    -> id in? ["zero", "isucc", "ipred", "one", "+", "-", "*", "<", ">", "<=", ">="]
   | "IntegerAux" -> id in? ["-"]  % unary minus
   | "Nat"        -> id in? ["succ", "pred", "+", "*"]
   | "Char"       -> id in? []
   | "String"     -> id in? ["^"]
   | "System"     -> id in? ["writeLine", "toScreen"]
   | "Function"   -> id in? []
   | "List"       -> id in? []

   %% Explicitly handcoded:
   | "Handcoded"  -> true

   | _ -> false

op builtinCType? (Qualified (q, id) : QualifiedId) : Bool =
 case q of
   | "Bool"          -> id in? ["Bool"]
   | "Integer"       -> id in? ["Int", "Int0", "Integer"]
   | "Nat"           -> id in? ["Nat", "PosNat", "Nat8", "Nat16", "Nat32"]
   | "Int"           -> id in? ["Int8", "Int16", "Int32"]
   | "Char"          -> id in? ["Char"]
   | "String"        -> id in? ["String"]
   | "List"          -> id in? []
   | "<unqualified>" -> id in? ["Ptr"]
   | _ -> false
      
%% TODO: Begin to deprecate this
op SpecTransform.sliceSpecForC (spc             : Spec)
                               (root_ops        : QualifiedIds)
                               (root_types      : QualifiedIds)
 : Spec =
 sliceSpecForCode (spc, root_ops, root_types, builtinCOp?, builtinCType?)

%% TODO: for now, transform is just for debugging
op SpecTransform.newSliceSpecForC (ms_spec         : Spec)
                                  (msg             : String)
                                  (root_ops        : QualifiedIds)
                                  (root_types      : QualifiedIds)
 : Spec =
 let slice = getSliceForCGen (ms_spec, root_ops, root_types) in
 let _     = describeSlice ("For C: " ^ msg, slice) in
 ms_spec
 
%% TODO: This will be used by other transforms
op getSliceForCGen (ms_spec    : Spec,
                    root_ops   : QualifiedIds,
                    root_types : QualifiedIds)
 : Slice =
 let
   def nameToQid name =
     case name of
       | [id]   -> mkUnQualifiedId id
       | [q,id] -> mkQualifiedId (q, id)
       | _ -> fail ("illegal name in Spec-To-C pragma: " ^ anyToString name)
 in
 let lms          = parseCTranslationPragmas ms_spec in
 let lm_data      = make_LMData              lms     in

 let type_macros    = foldl (fn (macro_names, ttrans) ->
                               % Target Term can be Name, Number, Apply, List, Vector, or Typed
                               case ttrans.target of
                                 | Name _ -> macro_names
                                 | _ -> (nameToQid ttrans.source) |> macro_names)
                            []
                            lm_data.type_translations
 in
 let op_macros    = foldl (fn (macro_names, otrans) ->
                             case otrans.target of
                               % Target Term can be Name, Number, Apply, List, Vector, or Typed
                               | Name _ -> macro_names
                               | _ -> (nameToQid otrans.source) |> macro_names)
                          []
                          lm_data.op_translations
 in
 let native_types = map (fn loc ->
                           nameToQid loc.name)
                        lm_data.native_types
 in
 let native_ops   = map (fn loc -> 
                           nameToQid loc.name) 
                        lm_data.native_ops 
 in
 let
   def primitive_type? name =
     if builtinCType? name then
       Some (Translated Primitive)
     else if name in? native_types then
       Some (Translated API)
     else if name in? type_macros then
       Some (Translated Macro)
     else
       None

   def primitive_op? name =
     if builtinCOp? name then
       Some (Translated Primitive)
     else if name in? native_ops then
       Some (Translated API)
     else if name in? op_macros then
       Some (Translated Macro)
     else
       None
 in
 let slice = {ms_spec         = ms_spec,
              op_map          = empty_op_map,
              type_map        = empty_type_map,
              pending_ops     = root_ops,
              pending_types   = root_types,
              primitive_op?   = primitive_op?,
              primitive_type? = primitive_type?}
 in
 completeSlice slice 

end-spec
