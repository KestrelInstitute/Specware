(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SimplifyForExecution qualifying spec
{

import /Languages/MetaSlang/CodeGen/DebuggingSupport

import /Languages/MetaSlang/CodeGen/Generic/SubstBaseSpecs              %  (1) Lisp C Java  subtBaseSpecs
import /Languages/MetaSlang/CodeGen/Generic/NormalizeTopLevelLambdas    %  (2) Lisp C Java  normalizeTopLevelLambdas
import /Languages/MetaSlang/CodeGen/Generic/InstantiateHOFns            %  (3) Lisp C Java  instantiateHOFns
import /Languages/MetaSlang/CodeGen/Generic/RemoveCurrying              %  (4)      C Java  removeCurrying
import /Languages/MetaSlang/CodeGen/Generic/LiftUnsupportedPatterns     %  (5)      C Java  liftUnsupportedPatterns [expand type restrictions into cases]
import /Languages/MetaSlang/CodeGen/Generic/PatternMatch                %  (6) Lisp C Java  translateMatch          (pattern match compiler)
import /Languages/MetaSlang/CodeGen/Generic/LambdaLift                  %  (7)      C Java  lambdaLift, lambdaLiftWithImportsSimulatingClosures
% import /Languages/MetaSlang/CodeGen/Generic/RecordMerge               %  (8) Lisp         expandRecordMerges
import /Languages/MetaSlang/CodeGen/Generic/LetWildPatToSeq             %  (9)      C Java  letWildPatToSeq
import /Languages/MetaSlang/CodeGen/Generic/ArityNormalize              % (10) Lisp         arityNormalize
import /Languages/MetaSlang/CodeGen/Generic/ConformOpDecls              % (11)      C Java  conformOpDecls
import /Languages/MetaSlang/CodeGen/Generic/EncapsulateProductArgs      % (12)      C Java  encapsulateProductArg
import /Languages/MetaSlang/CodeGen/Generic/RecordMerge                 % (13) Lisp C Java  introduceRecordMerges
import /Languages/MetaSlang/CodeGen/Generic/AddEqOps                    % (14)      C Java  addEqOps
import /Languages/MetaSlang/CodeGen/Generic/AddTypeConstructors         % (15)      C Java  addTypeConstructors
import /Languages/MetaSlang/CodeGen/Generic/NarrowTypes                 % (16) Lisp C Java  narrowTypes
import /Languages/MetaSlang/CodeGen/Generic/LiftSequences               % (17)      C Java  liftSequences
import /Languages/MetaSlang/CodeGen/Generic/RemoveGeneratedSuffixes     % (18) Lisp C Java  removeGeneratedSuffixes
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % (19) Lisp C Java  adjustElementOrder

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% simplifyForExecution performs a series of spec transforms that remove
%% various complications such as curried functions, higher order functions,
%% pattern matching, etc.
%%
%% The transforms within this are all individually invocable, allowing users to 
%% replicate this functionality step-by-step.
%%
%% Problems encountered along the way may be indicated via warning messages, 
%% but this transform always returns a spec (possibly the original one).
%%
%% There is no guarantee that the resulting spec will achieve all the intended
%% goals, so any translator which follows this must anticipate that contigency.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type TransformOptions = {remove_currying?           : Bool,  %  (4)
                         lift_unsupported_patterns? : Bool,  %  (5)
                         lambda_lift?               : Bool,  %  (7)
                         let_wild_pat_to_seq?       : Bool,  %  (9) 
                         arity_normalize?           : Bool,  % (10) 
                         conform_op_decls?          : Bool,  % (11) 
                         encapsulate_product_args?  : Bool,  % (12) 
                         add_eq_ops?                : Bool,  % (14) 
                         add_type_constructors?     : Bool,  % (15) 
                         lift_sequences?            : Bool}  % (17) 

op default_options : TransformOptions = 
 {remove_currying?           = true,  %  (4)
  lift_unsupported_patterns? = true,  %  (5)
  lambda_lift?               = true,  %  (7)
  let_wild_pat_to_seq?       = true,  %  (9) 
  arity_normalize?           = true,  % (10) 
  conform_op_decls?          = true,  % (11) 
  encapsulate_product_args?  = true,  % (12) 
  add_eq_ops?                = true,  % (14) 
  add_type_constructors?     = true,  % (15) 
  lift_sequences?            = true}  % (17) 

op SpecTransform.simplifyForExecution (ms_spec : Spec, options : TransformOptions) : Spec =

 let _ = showIfVerbose ["------------------------------------------",
                        "Simplifying spec for execution...",
                        "------------------------------------------"]
 in
 let _ = showSpecIfVerbose "Original" ms_spec in

 %% ==========================================================================================
 %% Fetch toplevel types and op early, to avoid including anything incidentally added later.
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

 let ms_spec = if options.remove_currying? then
                 let ms_spec = SpecTransform.removeCurrying ms_spec   in
                 let _   = showSpecIfVerbose "removeCurrying" ms_spec in
                  ms_spec
               else
                 ms_spec
 in 
  
 %% ==========================================================================================
 %%  (5) Lift Unsupported Patterns
 %%      Turn bodies of lambda's with restricted var types into case expressions.
 %%      Should preceed pattern match compiler that removes case expressions.
 %% ==========================================================================================

 let ms_spec = if options.lift_unsupported_patterns? then
                 let ms_spec = SpecTransform.liftUnsupportedPatterns   ms_spec in 
                 let _   = showSpecIfVerbose "liftUnsupportedPatterns" ms_spec in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %%  (6) Pattern Match Compiler, to remove case expressions.
 %%      Variant of Wadler's pattern matching compiler.
 %%
 %%      Currently introduces Select's and parallel Let bindings, which may confuse other
 %%      transforms.  
 %%
 %%      This may add calls to polymorphic fns, so must precede poly2mono. [TODO: verify this]
 %%      This may add local defs, so should preceed lambda lift.
 %%      This also does eta expansion,
 %% ==========================================================================================

 let ms_spec = SpecTransform.translateMatch  (ms_spec, true) in 
 let _  = showSpecIfVerbose "translateMatch"  ms_spec        in

 %% ==========================================================================================
 %%  (7) Lambda Lift
 %%      Move locally defined functions out to top level.
 %%      Should follow translateMatch,   which introduces local functions.
 %%      Should follow instantiateHOFns, which inlines local functions.
 %%      TODO: Could do in two parts: fully parameterize, then lift.
 %% ==========================================================================================

 let ms_spec = if options.lambda_lift? then
                 let ms_spec = SpecTransform.lambdaLift  ms_spec false in % don't simulate closures
                 let _  = showSpecIfVerbose "lambdaLift" ms_spec       in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %%  (9) Convert Lets of Wild Patterns to Seq's
 %%      'let _ = t1 in t2'   =>  '(t1;t2)'
 %% ==========================================================================================

 let ms_spec = if options.let_wild_pat_to_seq? then
                 let ms_spec = SpecTransform.letWildPatToSeq  ms_spec in 
                 let _  = showSpecIfVerbose "letWildPatToSeq" ms_spec in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %% (10) arityNormalize (TODO This does nothing?)
 %% ==========================================================================================

 let ms_spec = if options.arity_normalize? then
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %% (11) Conform Op Decls
 %%      Change def with multiple args to decompose single arg when decl has one (product) arg.
 %% ==========================================================================================

 let ms_spec = if options.conform_op_decls? then
                 let ms_spec = SpecTransform.conformOpDecls   ms_spec in 
                 let _   = showSpecIfVerbose "conformOpDecls" ms_spec in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %% (12) Encapsulate Product Args
 %%      Change call with multiple args to compose single arg when decl has one (product) arg.
 %% ==========================================================================================

 let ms_spec = if options.encapsulate_product_args? then
                 let ms_spec = SpecTransform.encapsulateProductArgs   ms_spec in 
                 let _   = showSpecIfVerbose "encapsulateProductArgs" ms_spec in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %% (13) Introduce Record Merges
 %%      Needed for stateful updates and globalize to work -- fodder for setf.
 %% ==========================================================================================

 let ms_spec = SpecTransform.introduceRecordMerges   ms_spec in 
 let _   = showSpecIfVerbose "introduceRecordMerges" ms_spec in

 %% ==========================================================================================
 %% (14) Add Eq Ops
 %%      Add equality ops for sums, products, etc. -- 
 %%      TODO: adds far too many (but removeUnusedOps removes them)
 %% ==========================================================================================

 let ms_spec = if options.add_eq_ops? then
                 let ms_spec = SpecTransform.addEqOps   ms_spec in 
                 let _   = showSpecIfVerbose "addEqOps" ms_spec in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %% (15) Add Type Constructors 
 %% ==========================================================================================

 let ms_spec = if options.add_type_constructors? then
                 let ms_spec = SpecTransform.addTypeConstructors   ms_spec in 
                 let _   = showSpecIfVerbose "addTypeConstructors" ms_spec in
                 ms_spec
               else
                 ms_spec
 in
  
 %% ==========================================================================================
 %% (16) Narrow Types
 %%      Retype terms such as (0 : Nat) to (0 : Nat1)
 %% ==========================================================================================
 %% TODO: This is horribly inefficient.

% let ms_spec = SpecTransform.narrowTypes  ms_spec in 
% let _  = showSpecIfVerbose "narrowTypes" ms_spec in

 %% ==========================================================================================
 %% (17) Lift Sequences
 %%      Lift statements above expressions, to avoid ugly C expressions using comma terms.
 %%      Transform 'f (a; b; c)' to '(a; b; f c)'
 %% ==========================================================================================

 let ms_spec = if options.lift_sequences? then
                 let ms_spec = SpecTransform.liftSequences  ms_spec in 
                 let _  = showSpecIfVerbose "liftSequences" ms_spec in
                 ms_spec
               else
                 ms_spec
 in

 %% ==========================================================================================
 %% (18) Remove Generated Suffixes
 %%      Simplify instroduced names such as "foo-1-1" to "foo" unless that causes conflicts.
 %% ==========================================================================================

 let ms_spec = SpecTransform.removeGeneratedSuffixes ms_spec in
 let _  = showSpecIfVerbose "removeGeneratedSuffixes" ms_spec in

 %% ==========================================================================================
 %% (19) Adjust Element Order
 %%      Topological sort the elements of the spec, to appease various compilers
 %% ==========================================================================================

 let ms_spec = SpecTransform.adjustElementOrder  ms_spec in
 let _  = showSpecIfVerbose "adjustElementOrder" ms_spec in

 ms_spec

}
