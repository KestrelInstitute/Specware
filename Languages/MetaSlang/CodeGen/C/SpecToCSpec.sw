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

op jlm () : () = ()

op verbose? : Bool = false

%% temporary hack until '#translate C' is working
op generateCSpecFromTransformedSpecHack (ms_spec    : Spec) 
                                        (app_name   : String) 
                                        (old_c_spec : C_Spec)
                                        (filter     : QualifiedId -> Bool) 
                                        (old_includes        : List String)
                                        (old_op_extern_types : List (String*String))
                                        (old_op_extern_defs  : List String)
 : Option C_Spec =
 let _ = jlm() in
 let lms             = parseCTranslationPragmas ms_spec     in
 let lm_verbatims    = extract_verbatims        lms         in 
 let lm_imports      = extract_imports          lms         in 
 let lm_translations = extract_translations     lms         in 
 let lm_natives      = extract_natives          lms         in 

 let includes        = map printImport          lm_imports  in
 %% 
 let _ = 
     if verbose? then
       let _ = writeLine "================================================================================" in
       let _ = writeLine "Verbatims in Pragmas:"                                                            in
       let _ = app (fn verbatim -> writeLine verbatim) lm_verbatims                                         in
       let _ = writeLine "================================================================================" in
       let _ = writeLine "Includes in emit_c_files:"                                                        in
       let _ = app (fn include -> writeLine include) old_includes                                           in
       let _ = writeLine "----------"                                                                       in
       let _ = writeLine "Includes in Pragmas:"                                                             in
       let _ = app (fn include -> writeLine include) includes                                               in
       let _ = writeLine "================================================================================" in
       let _ = writeLine "Translations in emit_c_files:"                                                    in
       let _ = app (fn (old,new) -> writeLine (old ^ " \t=> " ^ new)) old_op_extern_types                   in
       let _ = writeLine "----------"                                                                       in
       let _ = writeLine "Translations in Pragmas:"                                                         in
       let _ = app (fn trans -> writeLine (printTranslation trans)) lm_translations                         in
       let _ = writeLine "================================================================================" in
       let _ = writeLine "Natives in emit_c_files:"                                                         in
       let _ = app (fn str -> writeLine str) old_op_extern_defs                                             in
       let _ = writeLine "----------"                                                                       in
       let _ = writeLine "Natives in Pragmas:"                                                              in
       let _ = app (fn native -> writeLine (printNative native)) lm_natives                                 in
       let _ = writeLine "================================================================================" in
       ()
     else
       ()
 in
 let includes        = old_includes        in
 let op_extern_types = old_op_extern_types in
 let op_extern_defs  = old_op_extern_defs  in
 %% 
 let use_ref_types?  = true in
 let constructer_ops = []   in
 let ms_spec = renameTypes (ms_spec, op_extern_types) in
 let 
   def filter_wrt_extern_defs (qid as Qualified (q, id)) =
    filter qid && ~(id in? op_extern_defs)
 in
 let i2l_spec   = generateI2LCodeSpecFilter (ms_spec,
                                             use_ref_types?,
                                             constructer_ops,
                                             filter_wrt_extern_defs)
 in
 let new_c_spec = generateC4ImpUnitHack (i2l_spec,
                                         old_c_spec, 
                                         use_ref_types?,
                                         includes)
 in
 Some new_c_spec

op generateCSpecFromTransformedSpecIncrFilter (ms_spec    : Spec) 
                                              (app_name   : String) 
                                              (old_c_spec : C_Spec)
                                              (filter     : QualifiedId -> Bool) 
 : Option C_Spec =
 let use_ref_types?  = true in
 let constructer_ops = []   in

 let i2l_spec   = generateI2LCodeSpecFilter (ms_spec,
                                             use_ref_types?,
                                             constructer_ops,
                                             filter)
 in
 let new_c_spec = generateC4ImpUnit (i2l_spec,
                                    old_c_spec, 
                                    use_ref_types?)
 in
 Some new_c_spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Increment a pre-existing C_Spec from an already transformed MetaSlang spec.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromTransformedSpecIncr (ms_spec    : Spec) 
                                        (app_name   : String) 
                                        (old_c_spec : C_Spec)
 : Option C_Spec =
 let accept_all = (fn _ -> true) in
 generateCSpecFromTransformedSpecIncrFilter ms_spec app_name old_c_spec accept_all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C_Spec from an already transformed MetaSlang spec.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromTransformedSpec (ms_spec : Spec) (app_name : String) 
 : Option C_Spec =
 generateCSpecFromTransformedSpecIncr ms_spec app_name (emptyCSpec "")

end-spec
