CGen qualifying spec

import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L       % MetaSlang to I2L
import /Languages/I2L/CodeGen/C/I2LToC                   % I2L       to C

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C_Spec from an already transformed MetaSlang spec.
%% The filter function is used to selectively generate code only for those ops 
%% and types x for which filter(x) is true.
%% The C_Spec parameter is used for incremental code generation.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
