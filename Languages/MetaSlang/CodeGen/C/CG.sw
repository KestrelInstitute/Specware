(**
 * interface to the MetaSlang C code generator
 *)

CG qualifying
spec
  import SpecsToI2L
  import I2LToC
  import /Languages/MetaSlang/CodeGen/CodeGenTransforms
  import /Languages/MetaSlang/Transformations/RemoveCurrying
  import /Languages/MetaSlang/Transformations/LambdaLift
  import /Languages/MetaSlang/Transformations/InstantiateHOFns
  import /Languages/MetaSlang/Transformations/RecordMerge
  import /Languages/MetaSlang/Transformations/TheoryMorphism

% --------------------------------------------------------------------------------
% interface
% --------------------------------------------------------------------------------

  (**
   * performs the neccessary transformations on the MetaSlang spec spc as preparation
   * for the C code generation. The basespec is used to add the neccessary sorts and op
   * the base spec to the resulting spec.
   * op transformSpecForCodeGen: (*basespec:*)AnnSpec.Spec -> (*spc:*)AnnSpec.Spec -> AnnSpec.Spec 
   *)

  (**
   * same as transformSpecForCodeGen, only that the transformation step "addMissingFromBase"
   * is omitted, i.e. no ops and sorts are added from the base spec
   * op transformSpecForCodeGenNoAdd: AnnSpec.Spec -> AnnSpec.Spec
   *)

  (**
   * generates C code for the given spec and writes it into the given file.
   * If the filename is None, "cgenout.c" is taken.
   * The basespec is used to add the neccessary sorts and op
   * the base spec to the resulting spec.
   * The third argument is ignored (todo: eliminate 3rd parameter in calls to this op)
   * op generateCCode: (*basespec:*)AnnSpec.Spec * (*spc:*)AnnSpec.Spec * AnnSpec.Spec * Option String -> ()
   *)

  (**
   * generates the C_Spec for the given spec. The basespec is used to add the neccessary
   * sorts and op the base spec to the resulting cspec.
   * op generateCSpec: (*basespec:*)AnnSpec.Spec -> (*spc:*)AnnSpec.Spec -> C_Spec
   *)


  (**
   * generate a C_Spec from an already transformed MetaSlang spec
   * op generateCSpecFromTransformedSpec: AnnSpec.Spec -> C_Spec
   *)
  

  (**
   * generate a C_Spec from an already transformed MetaSlang spec,
   * the filter function is used to selectively generate code only
   * for those ops and sorts x for which filter(x) is true.
   * The C_Spec parameter is used for incremental code generation.
   * op generateCSpecFromTransformedSpecIncrFilter: C_Spec -> AnnSpec.Spec -> (QualifiedId -> Bool) -> C_Spec
   *)

  (**
   * same as generateCSpecFromTransformedSpec, only that the additional C_Spec
   * is used to lookup already existing definitions in the C_Spec
   * op generateCSpecFromTransformedSpecIncr: C_Spec -> AnnSpec.Spec -> C_Spec
   * op generateCSpecFromTransformedSpecEnv: AnnSpec.Spec -> Env C_Spec
   *)


  (**
   * print the given cspec to a .h and .c file. The filename is used as
   * base name for the generated file, if omitted it defaults to "cgenout"
   * op printToFile: C_Spec * Option String -> ()
   * op postProcessCSpec: C_Spec -> C_Spec
   *)


  (**
   * monadic version of printToFile
   * op printToFileEnv: C_Spec * Option String -> Env ()
   *)

  (**
   * transforms a MetaSlang sort to a C type
   * op sortToCType: C_Spec -> AnnSpec.Spec -> Sort -> (C_Spec * C_Type)
   *)

  (**
   * transforms a MetaSlang term to a C expression
   * op termToCExp: C_Spec -> AnnSpec.Spec -> MS.Term -> (C_Spec * C_Block * C_Exp)
   *)

  (**
   * returns the string representation of the qualified id
   * as it appears in the resulting cspec
   * op showQualifiedId: QualifiedId -> String
   *)


% --------------------------------------------------------------------------------

  op transformSpecForCodeGen  (base : Spec) (spc : Spec) : Spec =
    transformSpecForCodeGenAux base spc true

  def transformSpecForCodeGenNoAdd (spc : Spec) : Spec =
    transformSpecForCodeGenAux emptySpec spc false  % initialSpecInCat ??

  op c_precNumSteps: List Nat = [13, 14, 15, 20, 23, 25, 27, 30, 35, 1000]
  op c_convertPrecNum (sw_prec_num : Nat) : Nat =
    case leftmostPositionSuchThat (c_precNumSteps, fn step -> sw_prec_num < step) of
     | Some i -> i 
     | None -> 10

  op transformSpecForCodeGenAux (basespc             : Spec)
                                (spc                 : Spec) 
                                (addmissingfrombase? : Bool) 
    : Spec =
    let trans_table = thyMorphismMaps spc "C" c_convertPrecNum in
    %let _ = writeLine(";;; thyMorphismMaps = " ^ anyToString thyMorphismMaps) in
    %let _ = showSorts spc in
    %let _ = writeLine(";;; generating C code...") in
    %let _ = writeLine("-----------------------------------------------------------\n\n\n") in
    %let _ = writeLine("transforming spec for C code generation...") in
    %let _ = writeLine("\n\n\n-----------------------------------------------------------") in
    %let _ = writeLine(printSpec spc) in
    let spc = translateRecordMergeInSpec            spc in
   %let spc = identifyIntSorts                      spc in
    let spc = if addmissingfrombase? then addMissingFromBase (basespc, spc, builtinSortOp) else spc in
    let spc = removeCurrying                        spc in
    let spc = instantiateHOFns                      spc in
   %let spc = lambdaToInner                         spc in
    let spc = poly2mono                             (spc,false) in
    let spc = addEqOpsToSpec                        spc in
    let spc = lambdaLift                            (spc,true) in
    let (spc,constrOps) = addSortConstructorsToSpec spc in
    let spc = conformOpDecls                        spc in
    let spc = adjustAppl                            spc in
    let spc = instantiateHOFns                      spc in
    spc

  op generateCSpec (base : Spec) (spc : Spec) : C_Spec =
    let base = substBaseSpecs base              in
    let spc  = transformSpecForCodeGen base spc in
    generateCSpecFromTransformedSpec spc

  op generateCSpecFromTransformedSpec (spc : Spec) : C_Spec =
    let xcspc = emptyCSpec "" in
    generateCSpecFromTransformedSpecIncr xcspc spc

  op generateCSpecFromTransformedSpecIncr (xcspc : C_Spec) (spc : Spec) : C_Spec =
    let filter = (fn _ -> true) in
    generateCSpecFromTransformedSpecIncrFilter xcspc spc filter

  op generateCSpecFromTransformedSpecIncrFilter (xcspc : C_Spec) (spc : Spec) (filter : QualifiedId -> Bool) 
    : C_Spec =
    let useRefTypes = true                                                        in
    let constrOps   = []                                                          in
    let impunit     = generateI2LCodeSpecFilter(spc,useRefTypes,constrOps,filter) in
    let cspec       = generateC4ImpUnit(impunit, xcspc, useRefTypes)              in
    cspec

  op generateCSpecFromTransformedSpecEnv (spc : Spec) : Env C_Spec =
    return (generateCSpecFromTransformedSpec spc)

  op printToFile (cspec : C_Spec, optFile : Option String) : () =
    let filename =
        case optFile of
          | None          -> "cgenout.c"
          | Some filename -> filename
    in
    let len = length(filename) in
    let basename = if subFromTo (filename, len-2, len) = ".c" then
                     subFromTo (filename, 0, len-2)
		   else
                     filename
    in
    let _ = writeLine(";; writing generated code to "^basename^".[ch]...") in
    let cfilename = basename^".c" in
    let hfilename = basename^".h" in
    let (hdrcspc,cspc) = splitCSpec cspec  in
    let cspec = addInclude(cspc,hfilename) in
    let _ = printCSpecToFile (hdrcspc, hfilename) in
    printCSpecToFile (cspec, cfilename)

  op printToFileEnv (cspec : C_Spec, optFile : Option String) : Env () =
    return (printToFile (cspec, optFile))

  op generateCCode (base      : Spec, 
                    spc       : Spec, 
                    _(*full*) : Spec, 
                    optFile   : Option String) 
    : () =
    %let _ = writeLine(";; bit-string special translation is turned "^
    %		      (if bitStringSpecial then "on" else "off"))
    %in
    let cspec = generateCSpec base spc in
    printToFile (cspec, optFile)


  op sortToCType (cspc : C_Spec) (spc : Spec) (typ : Sort) : C_Spec * C_Type =
    %% note: these two defaultCgContext's are very different from each other:
    let ctxt1   = default_S2I_Context                  in 
    let ctxt2   = default_I2C_Context                  in
    let tyvars  = []                                   in
    let i2lType = type2itype (ctxt1, spc, tyvars, typ) in
    c4Type(ctxt2,cspc,i2lType)

  op termToCExp (cspc : C_Spec) (spc : Spec) (tm : MS.Term) 
    : C_Spec * C_Block * C_Exp =
    let block = ([],[]) in
    termToCExpB cspc spc block tm

  op termToCExpB (cspc : C_Spec) (spc : Spec) (block : C_Block) (tm : MS.Term) 
    : C_Spec * C_Block * C_Exp =
    let ctxt1  = default_S2I_Context              in
    let ctxt2  = default_I2C_Context              in
    let i2lExp = term2expression (ctxt1, spc, tm) in
    c4Expression (ctxt2, cspc, block, i2lExp)

  def showQualifiedId (qid as Qualified (q, id) : QualifiedId) : String =
    qname2id (q, id)

  op postProcessCSpec (cspc : C_Spec) : C_Spec =
    I2LToC.postProcessCSpec cspc


end-spec
