CGen qualifying spec

% import /Languages/MetaSlang/CodeGen/C/SpecToCSpec
import /Languages/MetaSlang/Transformations/Pragma
import /Languages/MetaSlang/Transformations/SliceSpec

op builtinCOp? (Qualified (q, id) : QualifiedId) : Bool =
 case q of
   | "Bool"       -> id in? ["true", "false", "~", "&&", "||", "=>", "<=>", "~="]
   | "Integer"    -> id in? ["zero", "isucc", "ipred", "one", "+", "-", "*", "<", ">", "<=", ">="]
   | "IntegerAux" -> id in? ["-"]  % unary minus
   | "Nat"        -> id in? ["succ", "pred", "+", "*"]
   | "Char"       -> id in? []
   | "String"     -> id in? ["^"]
   | "System"     -> id in? ["writeLine", "toScreen"]
   | "Function"   -> id in? []
   | "List"       -> id in? []
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
 let slice = sliceForCGen (ms_spec, root_ops, root_types) in
 let _     = describeSlice ("For C: " ^ msg, slice) in
 ms_spec
 
op defaultSliceForCGen (ms_spec : Spec) : Slice =
 let root_ops   = topLevelOps   ms_spec in
 let root_types = topLevelTypes ms_spec in
 sliceForCGen (ms_spec, root_ops, root_types)
 
%% TODO: This will be used by other transforms
op sliceForCGen (ms_spec    : Spec,
                 root_ops   : QualifiedIds,
                 root_types : QualifiedIds)
 : Slice =
 let lms     = parseCTranslationPragmas ms_spec in
 let lm_data = make_LMData              lms     in
 let
   def oracular_type_status pending_type =
     let name = pending_type.name in
     if builtinCType? name then
       Some (Translated Primitive)
     else if name in? lm_data.native_types then
       Some (Translated API)
     else if name in? lm_data.type_macros then
       Some (Translated Macro)
     else
       None

   def oracular_op_status pending_op =
     let name = pending_op.name in
     if builtinCOp? name then
       Some (Translated Primitive)
     else if name in? lm_data.native_ops then
       Some (Translated API)
     else if name in? lm_data.op_macros then
       Some (Translated Macro)
     else
       None
 in
 let pending_ops   = map (fn name ->
                            {name            = name, 
                             contextual_type = Any noPos, 
                             location        = noLoc})
                         root_ops
 in
 let pending_types = map (fn name -> 
                            {name     = name, 
                             location = noLoc})
                         root_types
 in
 let slice = {ms_spec              = ms_spec,
              lm_data              = lm_data,
              resolved_ops         = empty_resolved_ops,
              resolved_types       = empty_resolved_types,
              pending_ops          = pending_ops,
              pending_types        = pending_types,
              oracular_type_status = oracular_type_status,
              oracular_op_status   = oracular_op_status}
 in
 completeSlice slice 

op parseCTranslationPragmas (s : Spec) : LanguageMorphisms =
 foldlSpecElements (fn (lms, elt) ->
                      case elt of
                        | Pragma (p as ("#translate", body, "#end", _)) | isPragmaKind (body, "C") ->
                          (case parseLanguageMorphism body of
                             | Parsed lm -> 
                               lms ++ [lm]
                             | Error msg ->
                               let _ = writeLine("Error parsing C translation pragma: " ^ msg) in
                               lms
                             | result ->
                               let _ = writeLine "=======================================" in
                               let _ = writeLine "Unecognized result from parsing pragma:" in
                               let _ = writeLine body                                      in
                               let _ = writeLine " => "                                    in
                               let _ = writeLine (anyToString result)                      in
                               let _ = writeLine "=======================================" in
                               lms)
                        | _ ->
                          lms)
                   []
                   s.elements


end-spec
