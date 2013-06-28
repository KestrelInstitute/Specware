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

 %% ==========================================================================================
 %%  (1) refine (possibly unused) ops using List_Executable.sw, String_Executable.sw, etc.
 %% ==========================================================================================

 %% substBaseSpecs should preceed other transforms, so those other transforms can apply to 
 %% the substituted definitions

 let spc = SpecTransform.substBaseSpecs                            spc in
 let _   = showSpecIfVerbose "substBaseSpecs"                      spc in

 %% ==========================================================================================
 %%  (2) might as well remove theorems early [could be done at any time, or never]
 %% ==========================================================================================

 let spc = SpecTransform.removeTheorems                            spc in 
 let _   = showSpecIfVerbose "removeTheorems"                      spc in 

 %% ==========================================================================================
 %%  (3) slice unused types and ops early to minimize wasted motion 
 %% ==========================================================================================

 let spc = SpecTransform.sliceSpecForC                             spc top_ops top_types in
 let _   = showSpecIfVerbose "sliceSpecForC[1]"                    spc in
 
 %% ==========================================================================================
 %%  (4) op f: A -> B -> C  ==>  op f_1_1: A * B -> C, etc.
 %% ==========================================================================================

 let spc = SpecTransform.removeCurrying                            spc in 
 let _   = showSpecIfVerbose "removeCurrying"                      spc in
  
 %% ==========================================================================================
 %%  (5) convert patterned lambdas into case expressions
 %% ==========================================================================================

 let spc = SpecTransform.normalizeTopLevelLambdas                  spc in 
 let _   = showSpecIfVerbose "normalizeTopLevelLambdas"            spc in

 %% ==========================================================================================
 %%  (6) instantiate higher order functions
 %%
 %%      calls normalizeCurriedDefinitions and simplifySpec 
 %%      should precede lambdaLift, poly2mono
 %% ==========================================================================================

 let spc = SpecTransform.instantiateHOFns                          spc in 
 let _   = showSpecIfVerbose "instantiateHOFns"                    spc in
 
 %% ==========================================================================================
 %%  (7) should follow removeCurrying and instantiateHOFns, since less graceful implementation
 %% ==========================================================================================

 let spc = lambdaLift                                              spc true in 
 let _   = showSpecIfVerbose "lambdaLift"                          spc in
  
 %% ==========================================================================================
 %%  (8) Variant of Wadler's pattern matching compiler 
 %% ==========================================================================================

 %% Currently, translateMatch introduces Select's and parallel Let bindings,
 %% which would confuse other transforms.  So until that is changed, 
 %% translateMatch should be done late in the transformation sequence.
 %%
 %% We also might wish to convert matches to case or typecase expressions,
 %% in which case not all matches would be transformed to if statements.

 %% This may add calls to polymorphic fns, so must precede poly2mono.

 let spc = SpecTransform.translateMatch                            spc in 
 let _   = showSpecIfVerbose "translateMatch"                      spc in
 
 %% ==========================================================================================
 %%  (9) rewrite forms such as foo << {y = y} to {x = foo.x, y = y, z = foo.z}
 %% ==========================================================================================

 let spc = SpecTransform.expandRecordMerges                        spc in 
 let _   = showSpecIfVerbose "translateRecordMergeInSpec"          spc in
  
 %% ==========================================================================================
 %% (10) transforms "let _ = t1 in t2" into "(t1;t2)"
 %% ==========================================================================================

 let spc = SpecTransform.letWildPatToSeq                           spc in 
 let _   = showSpecIfVerbose "letWildPatToSeq"                     spc in
  
 %% ==========================================================================================
 %% (11) ??
 %% ==========================================================================================

 %% let spc = SpecTransform. unfoldTypeAliases                      spc in
 %% let _   = showSpecIfVerbose "unfoldTypeAliases"                spc in

 %% ==========================================================================================
 %% (12) should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons
 %% ==========================================================================================

 let spc = SpecTransform.expandTypeDefs                            spc in 
 let _   = showSpecIfVerbose "expandTypeDefs"                      spc in
  
 %% ==========================================================================================
 %% (13) should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons
 %% ==========================================================================================

 let spc = SpecTransform.removeNonNatSubtypes                      spc in 
 let _   = showSpecIfVerbose "removeNonNatSubtypes"                spc in
  
 %% ==========================================================================================
 %% (14) turn bodies of lambda's with restricted var types into case expressions 
 %% ==========================================================================================

 let spc = SpecTransform.liftUnsupportedPatterns                   spc in 
 let _   = showSpecIfVerbose "liftUnsupportedPatterns"             spc in

 %% ==========================================================================================
 %% (15) After this is called, we can no longer reason about polymorphic types such as List(a)
 %% ==========================================================================================

 let spc = SpecTransform.poly2monoAndDropPoly                      spc in 
 let _   = showSpecIfVerbose "poly2monoAndDropPoly"                spc in
  
 %% ==========================================================================================
 %% (16) generic optimizations -- inlining, remove dead code, etc. % TODO: move to end?
 %% ==========================================================================================

 let spc = SpecTransform.simplifySpec                              spc in 
 let _   = showSpecIfVerbose "simplifySpec"                        spc in
  
 %% ==========================================================================================
 %% (17) add equality ops for sums, products, etc. -- TODO: adds far too many (but removeUnusedOps removes them)
 %% ==========================================================================================

 let spc = SpecTransform.addEqOps                                  spc in 
 let _   = showSpecIfVerbose "addEqOps"                            spc in
  
 %% ==========================================================================================
 %% (18) remove newly introduced but unused ops (mainly eq ops) 
 %% ==========================================================================================

 let spc = SpecTransform.sliceSpecForC                             spc top_ops top_types in 
 let _   = showSpecIfVerbose "sliceSpecForC[2]"                    spc in 
  
 %% ==========================================================================================
 %% (19) these ops won't survive slicing, so this must follow removeUnusedOps
 %% ==========================================================================================

 let spc = SpecTransform.addTypeConstructors                       spc in 
 let _   = showSpecIfVerbose "addTypeConstructors"                 spc in
  
 %% ==========================================================================================
 %% (20) change def with multiple args to decompose single arg when decl has one (product) arg
 %% ==========================================================================================

 let spc = SpecTransform.conformOpDecls                            spc in 
 let _   = showSpecIfVerbose "conformOpDecls"                      spc in
  
 %% ==========================================================================================
 %% (21) Lisp: arityNormalize, Java: etaExpandDefs
 %% ==========================================================================================

 %% let spc = SpecTransform.etaExpandDefs                          spc in
 %% let _   = showSpecIfVerbose "etaExpandDefs"                    spc in

 %% ==========================================================================================
 %% (22) change call with multiple args to compose single arg when decl has one (product) arg
 %% ==========================================================================================

 let spc = SpecTransform.encapsulateProductArgs                    spc in 
 let _   = showSpecIfVerbose "adjustAppl"                          spc in
  
 %% ==========================================================================================
 %% (23) lambda lift again ??
 %% ==========================================================================================

 let spc = SpecTransform.lambdaLift                                spc false in 
 let _   = showSpecIfVerbose "lambdaLift[2]"                       spc in

 %% ==========================================================================================
 %% (25) expand pattern matches again ??
 %% ==========================================================================================

 let spc = SpecTransform.translateMatch                            spc in 
 let _   = showSpecIfVerbose "translateMatch[2]"                   spc in

 %% ==========================================================================================
 %% (26) 
 %% ==========================================================================================

 %% let spc = SpecTransform.distinctVariable                       spc in
 %% let _   = showSpecIfVerbose "distinctVariable"                 spc in

 spc

end-spec
