GCG qualifying spec

import /Languages/MetaSlang/CodeGen/CodeGenTransforms % ms spec => ms spec
import /Languages/MetaSlang/CodeGen/C/SliceForC       
import /Languages/MetaSlang/CodeGen/C/SpecToCSpec     % ms spec =>  c spec
import /Languages/C/PrintCSpec                        %  c spec =>  c files

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% generateCFiles is a side-effecting transform that returns the original 
%% metaslang spec. 
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

op SpecTransform.generateCFiles (ms_spec      : Spec, 
                                 app_name     : String,
                                 opt_filename : Option String)
 : Spec =
 let new_ms_spec = transformSpecTowardsC ms_spec                    in
 let _           = emitCFiles (new_ms_spec, app_name, opt_filename) in
 ms_spec

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
 let _ = showSpecIfVerbose "Original" ms_spec in

 %% ==========================================================================================
 %% fetch toplevel types and op early, to avoid including anything incidentally added later
 %% ==========================================================================================

 let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts ms_spec in 
 let _ = showIfVerbose ["toplevel ops: ", 
                        anyToString top_ops, 
                        "------------------------------------------"]
 in

 %% Phase 1: Add stuff

 %% ==========================================================================================
 %%  (1) Substitute Base Specs, to intoduce executable definitions
 %%      Refine (possibly unused) ops using List_Executable.sw, String_Executable.sw, etc.
 %% ==========================================================================================

 %% substBaseSpecs should preceed other transforms, so those other transforms can apply to 
 %% the substituted definitions

 let ms_spec = SpecTransform.substBaseSpecs   ms_spec in
 let _   = showSpecIfVerbose "substBaseSpecs" ms_spec in


 %% Phase 2: Spec to Spec transforms

 %% ==========================================================================================
 %%  (2) Normalize Top Level Lambdas
 %%      Convert patterned lambdas into case expressions.
 %% ==========================================================================================

 let ms_spec = SpecTransform.normalizeTopLevelLambdas   ms_spec in 
 let _   = showSpecIfVerbose "normalizeTopLevelLambdas" ms_spec in

 %% ==========================================================================================
 %%  (3) Instantiate Higher Order Functions
 %%      Calls normalizeCurriedDefinitions and simplifySpec.
 %%
 %%      Should precede removeCurrying, which eliminates higher order.
 %%      Should precede lambdaLift, which would remove inlineable local functions.
 %%      Should precede poly2mono, since higher order functions are usually polymorphic.
 %% ==========================================================================================

 let ms_spec = SpecTransform.instantiateHOFns   ms_spec in 
 let _   = showSpecIfVerbose "instantiateHOFns" ms_spec in

 %% ==========================================================================================
 %%  (4) Remove Currying
 %%      
 %%      'op f: A -> B -> C'  ==>  'op f_1_1: A * B -> C'
 %% ==========================================================================================

 let ms_spec = SpecTransform.removeCurrying   ms_spec in 
 let _   = showSpecIfVerbose "removeCurrying" ms_spec in
  
 %% ==========================================================================================
 %%  (5) Lift Unsupported Patterns
 %%      Turn bodies of lambda's with restricted var types into case expressions.
 %%      Should preceed pattern match compiler that removes case expressions.
 %% ==========================================================================================

 let ms_spec = SpecTransform.liftUnsupportedPatterns   ms_spec in 
 let _   = showSpecIfVerbose "liftUnsupportedPatterns" ms_spec in

 %% ==========================================================================================
 %%  (6) Pattern Match Compiler, to remove case expressions.
 %%      Variant of Wadler's pattern matching compiler.
 %%
 %%      Currently introduces Select's and parallel Let bindings, which may confuse other
 %%      transforms.  
 %%
 %%      This may add calls to polymorphic fns, so must precede poly2mono. [TODO: verify this]
 %%      This may add local defs, so should preceed lambda lift.
 %% ==========================================================================================

 let ms_spec = SpecTransform.translateMatch   (ms_spec, true) in 
 let _   = showSpecIfVerbose "translateMatch" ms_spec in

 %% ==========================================================================================
 %%  (7) Lambda Lift
 %%      Move locally defined functions out to top level.
 %%      Should follow translateMatch,   which introduces local functions.
 %%      Should follow instantiateHOFns, which inlines local functions.
 %% ==========================================================================================

 let ms_spec = SpecTransform.lambdaLift   ms_spec true in 
 let _   = showSpecIfVerbose "lambdaLift" ms_spec in
  
 %% ==========================================================================================
 %%  (8) Expand Record Merges
 %%      Make record constructions explicit.
 %%      'foo << {y = y}'   =>  '{x = foo.x, y = y, z = foo.z}'
 %%
 %%     This might be reversed later by introduceRecordMerges if we choose to produce Setf 
 %%     forms to revise mutable structures, but for now we stay within normal MetaSlang.
 %% ==========================================================================================

 let ms_spec = SpecTransform.expandRecordMerges   ms_spec in 
 let _   = showSpecIfVerbose "expandRecordMerges" ms_spec in
  
 %% ==========================================================================================
 %%  (9) Convert Lets of Wild Patterns to Seq's
 %%      'let _ = t1 in t2'   =>  '(t1;t2)'
 %% ==========================================================================================

 let ms_spec = SpecTransform.letWildPatToSeq   ms_spec in 
 let _   = showSpecIfVerbose "letWildPatToSeq" ms_spec in
  
 %% ==========================================================================================
 %% (10) Eta Expansion
 %% ==========================================================================================

 %% TODO: Verity conjecture that matchCon in translateMatch has already done eta expansion,
 %%       making this redundant.  If so, we can remove this.

 %% let ms_spec = SpecTransform.etaExpandDefs    ms_spec in  
 %% let _   = showSpecIfVerbose "etaExpandDefs"  ms_spec in

 %% ==========================================================================================
 %% (11) Arity Normalize
 %% ==========================================================================================

 %% For exmaple, revise
 %%
 %%  op f1 (x: Nat) (y: Nat, z: Nat) : Nat = x + y + z
 %%   =>
 %%  op f1 (x: Nat) (apV: Nat * Nat) : Nat = let x0 = apV in case (x0.1, x0.2) of (y, z) -> x + y + z
 %%
 %%  op g1 (x: Nat, y: Nat, z: Nat) : Nat = f1 x (y, z)
 %%   =>
 %%  op g1 (x: Nat, y: Nat, z: Nat) : Nat = f1 x (TranslationBuiltIn.mkTuple(y, z))'

 %% let ms_spec = SpecTransform.arityNormalize   ms_spec in
 %% let _   = showSpecIfVerbose "arityNormalize" ms_spec in

 %% ==========================================================================================
 %% (12) Conform Op Decls
 %%      Change def with multiple args to decompose single arg when decl has one (product) arg.
 %% ==========================================================================================

 let ms_spec = SpecTransform.conformOpDecls   ms_spec in 
 let _   = showSpecIfVerbose "conformOpDecls" ms_spec in

 %% ==========================================================================================
 %% (13) Encapsulate Product Args
 %%      Change call with multiple args to compose single arg when decl has one (product) arg.
 %% ==========================================================================================

 let ms_spec = SpecTransform.encapsulateProductArgs   ms_spec in 
 let _   = showSpecIfVerbose "encapsulateProductArgs" ms_spec in
  
 %% ==========================================================================================
 %% (14) Introduce Record Merges
 %% ==========================================================================================

 let ms_spec = SpecTransform.introduceRecordMerges   ms_spec in 
 let _   = showSpecIfVerbose "introduceRecordMerges" ms_spec in

 %% ==========================================================================================
 %% (15) Expand Type Defs
 %%      Should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons.
 %% ==========================================================================================

 let ms_spec = SpecTransform.expandTypeDefs   ms_spec in 
 let _   = showSpecIfVerbose "expandTypeDefs" ms_spec in
  
 %% ==========================================================================================
 %% (16) Revise Types for Code Generation
 %% ==========================================================================================

 let ms_spec = SpecTransform.reviseTypesForC   ms_spec in 
 let _   = showSpecIfVerbose "reviseTypesForC" ms_spec in
  
 %% ==========================================================================================
 %%  (-) Remove Polymorphism
 %%      After this is called, we can no longer reason about polymorphic types such as List(a).
 %% ==========================================================================================

 %% let ms_spec = SpecTransform.poly2monoAndDropPoly   ms_spec in 
 %% let _   = showSpecIfVerbose "poly2monoAndDropPoly" ms_spec in
  
 %% ==========================================================================================
 %%  (-) generic optimizations -- inlining, remove dead code, etc. % TODO: move to end?
 %% ==========================================================================================

 let ms_spec = SpecTransform.simplifySpec   ms_spec in 
 let _   = showSpecIfVerbose "simplifySpec" ms_spec in
  
 %% ==========================================================================================
 %% (17) Add Eq Ops
 %%      Add equality ops for sums, products, etc. -- 
 %%      TODO: adds far too many (but removeUnusedOps removes them)
 %% ==========================================================================================

 let ms_spec = SpecTransform.addEqOps   ms_spec in 
 let _   = showSpecIfVerbose "addEqOps" ms_spec in

 %% ==========================================================================================
 %% (18) Add Type Constructors 
 %% ==========================================================================================

 let ms_spec = SpecTransform.addTypeConstructors   ms_spec in 
 let _   = showSpecIfVerbose "addTypeConstructors" ms_spec in
  
 %% ==========================================================================================
 %% (19) slice unused types and ops 
 %% ==========================================================================================

 let ms_spec = SpecTransform.sliceSpecForC   ms_spec top_ops top_types in
 let _   = showSpecIfVerbose "sliceSpecForC" ms_spec                   in

 ms_spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% emitCfiles is an identity transform on metaslang specs, with the side-effect 
%% of possibly outputting C files directly from the provided metaslang spec.  
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

op SpecTransform.emitCFiles (ms_spec      : Spec,
                             app_name     : String,
                             opt_filename : Option String)
 : Spec =
 let (root_ops, root_types) = default_roots ms_spec in
 newEmitCFiles (ms_spec, app_name, root_ops, root_types, opt_filename)

op SpecTransform.newEmitCFiles (ms_spec      : Spec,
                                app_name     : String,
                                root_ops     : OpNames,
                                root_types   : TypeNames,
                                opt_filename : Option String)
 : Spec =
 let slice = sliceForCGen (ms_spec, root_ops, root_types) in
 let _ = describeSlice ("EMITTING", slice) in
 let _ = 
     case generateCSpecFromSlice (slice, app_name) of
       | Some c_spec ->
         printCSpec (c_spec, app_name, opt_filename) 
       | _ ->
         %% warning might be under control of various flags
         writeLine ("Unable to emit C files for " ^ app_name)
 in             
 ms_spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C spec from a MetaSlang spec
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% For debugging purposes only.  No one calls this.
op generateCSpec (ms_spec : Spec) (app_name : String) : Option C_Spec =
 let ms_spec = SpecTransform.transformSpecTowardsC ms_spec in
 let slice   = defaultSliceForCGen                 ms_spec in
 generateCSpecFromSlice (slice, app_name)


end-spec
