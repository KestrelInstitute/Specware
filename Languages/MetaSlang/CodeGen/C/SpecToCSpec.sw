CGen qualifying spec

import /Languages/SpecCalculus/Semantics/Evaluate/Translate  % translateSpec
import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L           % MetaSlang to I2L
import /Languages/I2L/CodeGen/C/I2LToC                       % I2L       to C

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

%% temporary hack until '#translate C' is working
op generateCSpecFromTransformedSpecHack (ms_spec    : Spec) 
                                        (app_name   : String) 
                                        (old_c_spec : C_Spec)
                                        (filter     : QualifiedId -> Bool) 
                                        (includes        : List String)
                                        (op_extern_types : List (String*String))
                                        (op_extern_defs  : List String)
 : Option C_Spec =
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
