CG qualifying spec

%% SpecTransforms:
import /Languages/MetaSlang/CodeGen/CodegenTransforms

 %% 
 import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L  % MetaSlang =codegen=> I2L
 import /Languages/I2L/CodeGen/C/I2LToC              % I2L       =codegen=> C

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

 let spc = lambdaLiftWithImportsSimulatingClosures                 spc in 
 let _   = showSpecIfVerbose "lambdaLiftWithImports"               spc in
  
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

 let spc = SpecTransform.adjustAppl                                spc in 
 let _   = showSpecIfVerbose "adjustAppl"                          spc in
  
 %% ==========================================================================================
 %% (23) lambda lift again ??
 %% ==========================================================================================

 let spc = SpecTransform.lambdaLiftWithImports                     spc in 
 let _   = showSpecIfVerbose "lambdaLiftWithImports[2]"            spc in

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate the C_Spec for the given spec. 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpec (app_name : String) (spc : Spec) : C_Spec =
 let spc  = transformSpecForCGen spc in
 generateCSpecFromTransformedSpec app_name spc 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Generate a C_Spec from an already transformed MetaSlang spec.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromTransformedSpec (app_name : String) (spc : Spec) : C_Spec =
 generateCSpecFromTransformedSpecIncr app_name spc (emptyCSpec "") 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% As above, but incremental -- the provided C_Spec is used to lookup already 
%% existing definitions.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op generateCSpecFromTransformedSpecIncr (app_name : String) 
                                         (spc      : Spec) 
                                         (xcspc    : C_Spec)
  : C_Spec =
  let filter = (fn _ -> true) in
  generateCSpecFromTransformedSpecIncrFilter app_name spc xcspc filter

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Generate a C_Spec from an already transformed MetaSlang spec.
 %% The filter function is used to selectively generate code only for those ops 
 %% and types x for which filter(x) is true.
 %% The C_Spec parameter is used for incremental code generation.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCSpecFromTransformedSpecIncrFilter (app_name : String) 
                                               (spc      : Spec) 
                                               (xcspc    : C_Spec)
                                               (filter   : QualifiedId -> Bool) 
  : C_Spec =
  let constrOps   = []                                                              in
  let useRefTypes = true                                                            in
  let impunit     = generateI2LCodeSpecFilter (spc, useRefTypes, constrOps, filter) in
  let cspec       = generateC4ImpUnit         (impunit, xcspc, useRefTypes)         in
  cspec

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Split the C spec into .c and .h portions and print those two files.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op printToFile (app_name     : String,
                 c_spec       : C_Spec,
                 opt_filename : Option String)
  : () =
  let filename =
      case opt_filename of
        | None          -> "cgenout.c"
        | Some filename -> filename
  in
  let len = length filename in
  let basename = if subFromTo (filename, len-2, len) = ".c" then
                   subFromTo (filename, 0, len-2)
                 else
                   filename
  in
  let _ = writeLine (";; writing generated code to " ^ basename ^ ".[ch]...") in

  let c_filename       = basename ^ ".c"    in
  let h_filename       = basename ^ ".h"    in
  let (h_spec, c_spec) = splitCSpec c_spec  in  

  let id_dfn           = ("Patched_PrismId", C_String, C_Const (C_Str basename)) in
  let h_spec           = addHeader    (h_spec, app_name)   in
  let h_spec           = addTrailer   (h_spec, app_name)   in
  let h_spec           = addConstDefn (h_spec, id_dfn)     in  

  let c_spec           = addHeader    (c_spec, app_name)   in
  let c_spec           = addTrailer   (c_spec, app_name)   in
  let c_spec           = addInclude   (c_spec, h_filename) in

  let _ = printCSpecAsHeaderToFile (h_spec, h_filename) in
  let _ = printCSpecToFile         (c_spec, c_filename) in
  ()

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Generate C code for the given spec and write it into the given file.
 %% If the filename is None, "cgenout.c" is taken.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCCode (app_name     : String,
                   spc          : Spec, 
                   opt_filename : Option String)
  : () =
  % for generation using CTarget, see evaluateGenCThin in Languages/SpecCalculus/Semantics/Specware.sw
  % if importsCTarget? spc then
  %   let _ = writeLine("Spec refers to CTarget, will use new C generator.") in
  %   let filename = case opt_filename of 
  %                    | Some filename -> filename 
  %                    | _ -> "testing" 
  %   in
  %   printSpecAsCToFile (filename, spc)
  % else
  let cspec = generateCSpec app_name spc in 
  printToFile (app_name, cspec, opt_filename)

 op SpecTransform.emitCCode (spc          : Spec, 
                             app_name     : String,
                             opt_filename : Option String)
  : Spec =
  let spc  = transformSpecForCGen spc in
  let cspec = generateCSpecFromTransformedSpec app_name spc in
  let _ = printToFile (app_name, cspec, opt_filename) in
  spc

end-spec
