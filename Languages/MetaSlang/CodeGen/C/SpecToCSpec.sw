CGen qualifying spec

import /Languages/SpecCalculus/Semantics/Evaluate/Translate  % translateSpec
import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L           % MetaSlang to I2L
import /Languages/I2L/CodeGen/C/I2LToC                       % I2L       to C
import /Languages/MetaSlang/Transformations/Pragma           % for selecting pragmas
import /Languages/MetaSlang/CodeGen/LanguageMorphism         % for parsing   pragmas

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C_Spec from an already transformed MetaSlang spec.
%% The filter function is used to selectively generate code only for those ops 
%% and types x for which filter(x) is true.
%% The C_Spec parameter is used for incremental code generation.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(*
 *  op  translateSpec : Bool -> Spec -> Renaming -> QualifiedIds -> Bool -> Option UnitId -> Env Spec
 *  def  allow_exceptions? spc renaming immune_op_names allow_extra_rules? currentUID? = 
 *)

op renameTypes (ms_spec : Spec, renamings : List (String * String)) : Spec =
 let rules = map (fn (old, new) -> 
                    let new = mkUnQualifiedId new in
                    (Type (mkUnQualifiedId old, new, [new]), 
                     noPos))
                 renamings
 in
 let renaming = (rules, noPos) in

 let revised_spec = run (translateSpec false         % allow_exceptions? 
                                       ms_spec
                                       renaming 
                                       []            % immune_op_names 
                                       false         % allow_extra_rules? 
                                       None)         % currentUID?
 in

 %% TODO: The spec term for the resulting spc is something like 'translate foo by {....}',
 %%       where foo is the name of the spec before all the various other transforms have been done,
 %%       and does not mention those transforms.  (Hence evaluating that term would not produce this spec.)
 %%       It seems that those transforms are not appearing in the term describing the transformed specs.
 %% let _ = writeLine(printSpec spc) in

 revised_spec

op generateCSpecFromTransformedSpecIncrFilter (ms_spec       : Spec) 
                                              (app_name      : String) 
                                              (old_c_spec    : C_Spec)
                                              (desired_type? : QualifiedId -> Bool) 
                                              (desired_op?   : QualifiedId -> Bool) 

 : Option C_Spec =
 let lms = parseCTranslationPragmas ms_spec in
 
 let use_ref_types?  = false in
 let constructer_ops = []   in
 %% let ms_spec = renameTypes (ms_spec, op_extern_types) in
 let natives      = extractNatives         lms                  in
 let translations = extractTranslations    lms                  in
 let translations = markNativeTranslations translations natives in
 let i2l_spec     = generateI2LCodeSpecFilter (ms_spec,
                                               use_ref_types?,
                                               constructer_ops,
                                               desired_type?,
                                               desired_op?,
                                               lms,
                                               natives,
                                               translations)
 in
 let new_c_spec   = generateC4ImpUnit (i2l_spec,
                                       old_c_spec, 
                                       use_ref_types?,
                                       lms,
                                       translations)
 in
 Some new_c_spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Increment a pre-existing C_Spec from an already transformed MetaSlang spec.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromTransformedSpecIncr (ms_spec    : Spec) 
                                        (app_name   : String) 
                                        (old_c_spec : C_Spec)
 : Option C_Spec =
 let 
  def desired_type? _ = true 
  def desired_op?   _ = true
 in
 generateCSpecFromTransformedSpecIncrFilter ms_spec 
                                            app_name
                                            old_c_spec 
                                            desired_type?
                                            desired_op?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C_Spec from an already transformed MetaSlang spec.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromTransformedSpec (ms_spec : Spec) (app_name : String) 
 : Option C_Spec =
 let old_c_spec = emptyCSpec "" in
 generateCSpecFromTransformedSpecIncr ms_spec app_name old_c_spec

end-spec
