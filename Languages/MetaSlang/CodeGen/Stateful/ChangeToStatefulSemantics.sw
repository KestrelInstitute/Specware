Stateful qualifying spec

import /Languages/MetaSlang/CodeGen/Generic/DeconflictUpdates  %  (B) Lisp C Java  deconflictUpdates
import /Languages/MetaSlang/CodeGen/Stateful/StatefulUpdates   %  (C) Lisp C Java  makeUpdatesStateful
import /Languages/MetaSlang/CodeGen/Stateful/Globalize         %  (D) Lisp C Java  globalize

op SpecTransform.makeExecutionStateful (ms_spec             : Spec, 
                                        root_op_names       : OpNames, 
                                        stateful_type_names : TypeNames,
                                        global_type_name    : TypeName,
                                        opt_global_var_id   : Option Id,
                                        opt_ginit           : Option OpName,
                                        tracing?            : Bool)
 : Spec =
 let global_var_id = 
     case opt_global_var_id of
       | Some id -> id
       | _ -> "implicitly_generated_global_var"
 in

 let _ = showIfVerbose ["------------------------------------------",
                        "Making execution stateful...",
                        "------------------------------------------"]
 in
 let _ = showSpecIfVerbose "Original" ms_spec in

 let ms_spec_2       = SpecTransform.deconflictUpdates   (ms_spec,         root_op_names, stateful_type_names,                        tracing?) in
 let stateful_spec_1 = SpecTransform.makeUpdatesStateful (ms_spec_2,       root_op_names, stateful_type_names,                        tracing?) in
 let stateful_spec_2 = SpecTransform.globalize           stateful_spec_1  (root_op_names, global_type_name, global_var_id, opt_ginit, tracing?) in
 let stateful_spec_3 = SpecTransform.simplifySpec        stateful_spec_2         in
 let stateful_spec_4 = SpecTransform.expandRecordMerges  stateful_spec_3         in  % non-stateful record merges may survive globalize 
 let stateful_spec_5 = SpecTransform.normalizeTypes     (stateful_spec_4, false) in
 stateful_spec_4

end-spec
