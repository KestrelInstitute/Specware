(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

CGen qualifying spec

import /Languages/SpecCalculus/Semantics/Evaluate/Translate  % translateSpec
import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L           % MetaSlang to I2L
import /Languages/I2L/CodeGen/C/I2LToC                       % I2L       to C
import /Languages/MetaSlang/CodeGen/C/SliceForC

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

op renameTypes (ms_spec   : Spec, 
                renamings : List (String * String)) 
 : Spec =
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C_Spec from an already transformed MetaSlang spec.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromSlice (slice : Slice) : Option C_Spec =
 let i2l_spec   = generateI2LCodeSpecFilter slice             in
 let new_c_spec = generateC4ImpUnit         (i2l_spec, slice) in
 Some new_c_spec

end-spec
