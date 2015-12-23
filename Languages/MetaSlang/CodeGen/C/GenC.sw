(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

GCG qualifying spec

import /Languages/MetaSlang/CodeGen/C/SliceForC       

import /Languages/MetaSlang/CodeGen/Generic/SimplifyForExecution       %       ms spec =>       ms spec
import /Languages/MetaSlang/CodeGen/Stateful/ChangeToStatefulSemantics %       ms_spec => stateful spec
import /Languages/MetaSlang/CodeGen/C/SpecToCSpec                      % stateful spec =>        c spec
import /Languages/C/PrintCSpec                                         %        c spec =>        c files

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% generateCFiles is a side-effecting transform. 
%%
%% It generate C code for the given spec and writes it into the appropriate
%% .h and .c files.
%%
%% (If the filename is None, "cgenout.c" is used.)
%%
%% It may fail to do anything for problematic specs.
%%
%% For generation using CTarget, see evaluateGenCThin in 
%%   Languages/SpecCalculus/Semantics/Specware.sw
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.generateCFiles (ms_spec : Spec, filename : String) : () =
 let new_ms_spec = transformSpecTowardsC ms_spec                    in
 let _           = emitCFiles (new_ms_spec, filename) in
 ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% transformSpecTowardsC performs a series of spec transforms with the ntention 
%% of producing a a metaslang spec suitable for immediate production of C files.
%%
%% The transforms within transformSpecTowardsC are all individually invocable,
%% allowing users to replicate this functionality step-by-step.
%%
%% Problems encountered along the way may be indicated via warning messages, 
%% but this transform always returns a spec (possibly the original one).
%%
%% There is no guarantee that the resulting spec will be suitable for code 
%% production, so any SpecToC translator which follows this must anticipate 
%% that contigency.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.transformSpecTowardsC (ms_spec : Spec) : Spec =

 let _ = showIfVerbose ["------------------------------------------",
                        "transforming spec for C code generation...",
                        "------------------------------------------"]
 in
 let ms_spec = explicateEmbeds ms_spec in
 let ms_spec = removeImplicitConstructorOps ms_spec in
 let options = default_options in	% all transforms turned on
 SpecTransform.simplifyForExecution (ms_spec, options)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% emitCfiles is an side-effecting transform on metaslang specs, that
%% possibly outputs C files directly from the provided metaslang spec.  
%%
%% The provided metaslang spec might have been produced manually, or by an 
%% invocation of transformSpecTowardsC, or by a series of more detailed 
%% transformations.  
%%
%% emitCFiles should be as simple and direct as possible, and might emit no
%% files if the provided metaslang spec fails to obey appropriate restrictions.
%%
%% The motivation for having this as a distinct transform is that we may wish
%% to first transform the MetaSlang spec, then print it out for examination,
%% then generate C files.
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op default_roots (ms_spec : Spec) : OpNames * TypeNames = 
 all_ops_and_types ms_spec

op all_ops_and_types (ms_spec : Spec) : OpNames * TypeNames = 
 let op_names = 
     foldriAQualifierMap (fn (_, _, info, names) ->
                            (primaryOpName info) |> names)
                         []
                         ms_spec.ops
 in
 let type_names = 
     foldriAQualifierMap (fn (_, _, info, names) ->
                            (primaryTypeName info) |> names)
                         []
                         ms_spec.types
 in
 (op_names, type_names)

op SpecTransform.emitCFiles (ms_spec : Spec, filename : String) : () =
 let (root_ops, root_types) = default_roots ms_spec in
 newEmitCFiles (ms_spec, root_ops, root_types, filename)

op SpecTransform.newEmitCFiles (ms_spec    : Spec,
                                root_ops   : OpNames,
                                root_types : TypeNames,
                                filename   : String)
 : () =
 let slice = sliceForCGen (ms_spec, root_ops, root_types) in
 let _ = describeSlice ("EMITTING", slice) in
 let _ = 
     case generateCSpecFromSlice slice of
       | Some c_spec ->
         printCSpec (c_spec, filename) 
       | _ ->
         %% warning might be under control of various flags
         writeLine ("ERROR: Unable to emit C files for " ^ filename)
 in             
 ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C spec from a MetaSlang spec
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.genC (original_ms_spec    : Spec,
                       root_op_names       : OpNames, 
                       root_op_names_b     : OpNames, 
                       stateful_type_names : TypeNames,
                       global_type_name    : TypeName,
                       opt_global_var_id   : Option Id,
                       opt_ginit           : Option OpName,
                       filename            : String,
                       tracing?            : Bool)
 : () =
 let ms_spec       = SpecTransform.transformSpecTowardsC original_ms_spec in
 let stateful_spec = SpecTransform.makeExecutionStateful (ms_spec,
                                                          root_op_names,
                                                          stateful_type_names,
                                                          global_type_name,
                                                          opt_global_var_id,
                                                          opt_ginit,
                                                          tracing?)
 in
 let _             = SpecTransform.newEmitCFiles         (stateful_spec, 
                                                          root_op_names_b, 
                                                          [],
                                                          filename) 
 in
 ()

end-spec
