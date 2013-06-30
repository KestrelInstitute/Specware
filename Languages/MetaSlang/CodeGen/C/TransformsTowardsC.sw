CGen qualifying spec

%% SpecTransforms:
import /Languages/MetaSlang/CodeGen/CodeGenTransforms

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Transform MetaSlang spec in preparation for C code generation. 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.transformSpecForCGen (spc : Spec) : Spec =

 let _ = showIfVerbose ["------------------------------------------",
                        "transforming spec for C code generation...",
                        "------------------------------------------"]
 in
 let _ = showSpecIfVerbose "Original"                              spc in

 %% ==========================================================================================
 %% fetch toplevel types and op early, to avoid including anything incidentally added later
 %% ==========================================================================================

 let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in 
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

 let spc = SpecTransform.substBaseSpecs                            spc in
 let _   = showSpecIfVerbose "substBaseSpecs"                      spc in


 %% Phase 2: Spec to Spec transforms

 %% ==========================================================================================
 %%  (2) Normalize Top Level Lambdas
 %%      Convert patterned lambdas into case expressions.
 %% ==========================================================================================

 let spc = SpecTransform.normalizeTopLevelLambdas                  spc in 
 let _   = showSpecIfVerbose "normalizeTopLevelLambdas"            spc in

 %% ==========================================================================================
 %%  (3) Instantiate Higher Order Functions
 %%      Calls normalizeCurriedDefinitions and simplifySpec.
 %%
 %%      Should precede removeCurrying, which eliminates higher order.
 %%      Should precede lambdaLift, which would remove inlineable local functions.
 %%      Should precede poly2mono, since higher order functions are usually polymorphic.
 %% ==========================================================================================

 let spc = SpecTransform.instantiateHOFns                          spc in 
 let _   = showSpecIfVerbose "instantiateHOFns"                    spc in

 %% ==========================================================================================
 %%  (4) Remove Currying
 %%      
 %%      'op f: A -> B -> C'  ==>  'op f_1_1: A * B -> C'
 %% ==========================================================================================

 let spc = SpecTransform.removeCurrying                            spc in 
 let _   = showSpecIfVerbose "removeCurrying"                      spc in
  
 %% ==========================================================================================
 %%  (5) Lift Unsupported Patterns
 %%      Turn bodies of lambda's with restricted var types into case expressions.
 %%      Should preceed pattern match compiler that removes case expressions.
 %% ==========================================================================================

 let spc = SpecTransform.liftUnsupportedPatterns                   spc in 
 let _   = showSpecIfVerbose "liftUnsupportedPatterns"             spc in

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

 let spc = SpecTransform.translateMatch                            spc in 
 let _   = showSpecIfVerbose "translateMatch"                      spc in

 %% ==========================================================================================
 %%  (7) Lambda Lift
 %%      Move locally defined functions out to top level.
 %%      Should follow translateMatch,   which introduces local functions.
 %%      Should follow instantiateHOFns, which inlines local functions.
 %% ==========================================================================================

 let spc = lambdaLift                                              spc true in 
 let _   = showSpecIfVerbose "lambdaLift"                          spc in
  
 %% ==========================================================================================
 %%  (8) Expand Record Merges
 %%      Make record constructions explicit.
 %%      'foo << {y = y}'   =>  '{x = foo.x, y = y, z = foo.z}'
 %%
 %%     This might be reversed later by introduceRecordMerges if we choose to produce Setf 
 %%     forms to revise mutable structures, but for now we stay within normal MetaSlang.
 %% ==========================================================================================

 let spc = SpecTransform.expandRecordMerges                        spc in 
 let _   = showSpecIfVerbose "translateRecordMergeInSpec"          spc in
  
 %% ==========================================================================================
 %%  (9) Convert Lets of Wild Patterns to Seq's
 %%      'let _ = t1 in t2'   =>  '(t1;t2)'
 %% ==========================================================================================

 let spc = SpecTransform.letWildPatToSeq                           spc in 
 let _   = showSpecIfVerbose "letWildPatToSeq"                     spc in
  
 %% ==========================================================================================
 %% (10) Eta Expansion
 %% ==========================================================================================

 %% TODO: Verity conjecture that matchCon in translateMatch has already done eta expansion,
 %%       making this redundant.  If so, we can remove this.

 %% let spc = SpecTransform.etaExpandDefs                          spc in  
 %% let _   = showSpecIfVerbose "etaExpandDefs"                    spc in

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

 %% let spc = SpecTransform.arityNormalize                         spc in
 %% let _   = showSpecIfVerbose "arityNormalize"                   spc in

 %% ==========================================================================================
 %% (12) Conform Op Decls
 %%      Change def with multiple args to decompose single arg when decl has one (product) arg.
 %% ==========================================================================================

 let spc = SpecTransform.conformOpDecls                            spc in 
 let _   = showSpecIfVerbose "conformOpDecls"                      spc in

 %% ==========================================================================================
 %% (13) Encapsulate Product Args
 %%      Change call with multiple args to compose single arg when decl has one (product) arg.
 %% ==========================================================================================

 let spc = SpecTransform.encapsulateProductArgs                    spc in 
 let _   = showSpecIfVerbose "adjustAppl"                          spc in
  
 %% ==========================================================================================
 %% (14) Introduce Record Merges
 %% ==========================================================================================

 let spc = SpecTransform.introduceRecordMerges                     spc in 
 let _   = showSpecIfVerbose "introduceRecordMerges"               spc in

 %% ==========================================================================================
 %% (15) Expand Type Defs
 %%      Should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons.
 %% ==========================================================================================

 let spc = SpecTransform.expandTypeDefs                            spc in 
 let _   = showSpecIfVerbose "expandTypeDefs"                      spc in
  
 %% ==========================================================================================
 %% (16) Revise Types for Code Generation
 %% ==========================================================================================

 % let spc = SpecTransform.removeNonNatSubtypes                    spc in 
 let spc = SpecTransform.reviseTypesForC                           spc in 
 let _   = showSpecIfVerbose "removeNonNatSubtypes"                spc in
  
 %% ==========================================================================================
 %%  (-) Remove Polymorphism
 %%      After this is called, we can no longer reason about polymorphic types such as List(a).
 %% ==========================================================================================

 %% let spc = SpecTransform.poly2monoAndDropPoly                   spc in 
 %% let _   = showSpecIfVerbose "poly2monoAndDropPoly"             spc in
  
 %% ==========================================================================================
 %%  (-) generic optimizations -- inlining, remove dead code, etc. % TODO: move to end?
 %% ==========================================================================================

 let spc = SpecTransform.simplifySpec                              spc in 
 let _   = showSpecIfVerbose "simplifySpec"                        spc in
  
 %% ==========================================================================================
 %% (17) Add Eq Ops
 %%      Add equality ops for sums, products, etc. -- 
 %%      TODO: adds far too many (but removeUnusedOps removes them)
 %% ==========================================================================================

 let spc = SpecTransform.addEqOps                                  spc in 
 let _   = showSpecIfVerbose "addEqOps"                            spc in

 %% ==========================================================================================
 %% (18) Add Type Constructors 
 %% ==========================================================================================

 let spc = SpecTransform.addTypeConstructors                       spc in 
 let _   = showSpecIfVerbose "addTypeConstructors"                 spc in
  
 %% ==========================================================================================
 %% (19) slice unused types and ops 
 %% ==========================================================================================

 %% slice? is true for gen-lisp-top, false for gen-lisp and lgen-lisp

 let spc = SpecTransform.sliceSpecForC                             spc top_ops top_types in
 let _   = showSpecIfVerbose "sliceSpecForC"                       spc in

 spc

end-spec
