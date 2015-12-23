(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Stateful qualifying spec

import /Languages/MetaSlang/CodeGen/Stateful/AddMutex                % should preceed StatefulUpdates, Globalize

import /Languages/MetaSlang/CodeGen/Generic/DeconflictUpdates        % (1) Lisp C Java  deconflictUpdates
import /Languages/MetaSlang/CodeGen/Stateful/StatefulUpdates         % (2) Lisp C Java  makeUpdatesStateful
import /Languages/MetaSlang/CodeGen/Stateful/Globalize               % (3) Lisp C Java  globalize
import /Languages/MetaSlang/CodeGen/Generic/RecordMerge              % (4) Lisp         expandRecordMerges

import /Languages/MetaSlang/CodeGen/Generic/LiftSequences            % (6)      C Java  liftSequences

import /Languages/MetaSlang/CodeGen/Generic/RemoveGeneratedSuffixes  % (8) Lisp C Java  removeGeneratedSuffix

% import /Languages/SpecCalculus/AbstractSyntax/CheckSpec

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

 % This first one could be moved to CodeGen/Generic/SimplifyForExecution.sw (it remains in the "pure" Metaslang language):
 let ms_spec_2     = SpecTransform.deconflictUpdates       (ms_spec,        root_op_names, stateful_type_names,                        tracing?) in % (1)
 let stateful_spec = SpecTransform.makeUpdatesStateful     (ms_spec_2,      root_op_names, stateful_type_names,                        tracing?) in % (2)
 let stateful_spec = SpecTransform.globalize                stateful_spec  (root_op_names, global_type_name, global_var_id, opt_ginit, tracing?) in % (3)
 let stateful_spec = SpecTransform.expandRecordMerges       stateful_spec         in  % (4) non-stateful record merges may survive globalize 
 let stateful_spec = SpecTransform.simplifySpec             stateful_spec         in  % (5) perhaps not needed
 let stateful_spec = SpecTransform.liftSequences            stateful_spec         in  % (6)                                                      % todo: why is this needed again here?
 let stateful_spec = SpecTransform.normalizeTypes          (stateful_spec, false) in  % (7) reintroduce names for otherwise anonymous structures % todo: why is this needed again here?
 let stateful_spec = SpecTransform.removeGeneratedSuffixes  stateful_spec         in  % (8) simplify names (e.g., "foo-1-1" => "foo")            % todo: why is this needed again here?
 % let _ = checkSpecCore (stateful_spec, "testing") in
 stateful_spec

end-spec
