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

% --------------------------------------------------------------------------------
% interface
% --------------------------------------------------------------------------------

  (**
   * performs the neccessary transformations on the MetaSlang spec spc as preparation
   * for the C code generation. The basespec is used to add the neccessary sorts and op
   * the base spec to the resulting spec.
   *)
  op transformSpecForCodeGen: (*basespec:*)AnnSpec.Spec -> (*spc:*)AnnSpec.Spec -> AnnSpec.Spec 

  (**
   * same as transformSpecForCodeGen, only that the transformation step "addMissingFromBase"
   * is omitted, i.e. no ops and sorts are added from the base spec
   *)
  op transformSpecForCodeGenNoAdd: AnnSpec.Spec -> AnnSpec.Spec

  (**
   * generates C code for the given spec and writes it into the given file.
   * If the filename is None, "cgenout.c" is taken.
   * The basespec is used to add the neccessary sorts and op
   * the base spec to the resulting spec.
   * The third argument is ignored (todo: eliminate 3rd parameter in calls to this op)
   *)
  op generateCCode: (*basespec:*)AnnSpec.Spec * (*spc:*)AnnSpec.Spec * AnnSpec.Spec * Option(String) -> ()

  (**
   * generates the CSpec for the given spec. The basespec is used to add the neccessary
   * sorts and op the base spec to the resulting cspec.
   *)
  op generateCSpec: (*basespec:*)AnnSpec.Spec -> (*spc:*)AnnSpec.Spec -> CSpec

  (**
   * generate a CSpec from an already transformed MetaSlang spec
   *)
  op generateCSpecFromTransformedSpec: AnnSpec.Spec -> CSpec

  (**
   * generate a CSpec from an already transformed MetaSlang spec,
   * the filter function is used to selectively generate code only
   * for those ops and sorts x for which filter(x) is true.
   * The CSpec parameter is used for incremental code generation.
   *)
  op generateCSpecFromTransformedSpecIncrFilter: CSpec -> AnnSpec.Spec -> (QualifiedId -> Boolean) -> CSpec

  (**
   * same as generateCSpecFromTransformedSpec, only that the additional CSpec
   * is used to lookup already existing definitions in the CSpec
   *)
  op generateCSpecFromTransformedSpecIncr: CSpec -> AnnSpec.Spec -> CSpec

  op generateCSpecFromTransformedSpecEnv: AnnSpec.Spec -> Env CSpec

  (**
   * print the given cspec to a .h and .c file. The filename is used as
   * base name for the generated file, if omitted it defaults to "cgenout"
   *)
  op printToFile: CSpec * Option(String) -> ()

  op postProcessCSpec: CSpec -> CSpec

  (**
   * monadic version of printToFile
   *)
  op printToFileEnv: CSpec * Option(String) -> Env ()

  (**
   * transforms a MetaSlang sort to a C type
   *)
  op sortToCType: CSpec -> AnnSpec.Spec -> Sort -> (CSpec * CType)

  (**
   * transforms a MetaSlang term to a C expression
   *)
  op termToCExp: CSpec -> AnnSpec.Spec -> MS.Term -> (CSpec * Block * CExp)

  (**
   * returns the string representation of the qualified id
   * as it appears in the resulting cspec
   *)
  op showQualifiedId: QualifiedId -> String


% --------------------------------------------------------------------------------

  def transformSpecForCodeGen basespc spc =
    transformSpecForCodeGenAux basespc spc true

  def transformSpecForCodeGenNoAdd spc =
    transformSpecForCodeGenAux emptySpec spc false

  op transformSpecForCodeGenAux: AnnSpec.Spec -> AnnSpec.Spec -> Boolean -> AnnSpec.Spec
  def transformSpecForCodeGenAux basespc spc addmissingfrombase? =
    %let _ = showSorts spc in
    %let _ = writeLine("-----------------------------------------------------------\n\n\n") in
    %let _ = writeLine("transforming spec for C code generation...") in
    %let _ = writeLine("\n\n\n-----------------------------------------------------------") in
    %let _ = writeLine(printSpec spc) in
    let spc = identifyIntSorts spc in
    let spc = if addmissingfrombase?
		then addMissingFromBase(basespc,spc,builtinSortOp)
	      else spc
    in
    let spc = removeCurrying spc in
    let spc = lambdaToInner spc in
    let spc = poly2mono(spc,false) in
    %let _ = writeLine(printSpec spc) in
    let spc = addEqOpsToSpec spc in
    %let _ = printSpecWithSortsToTerminal spc in
    let spc = lambdaLift spc in
    let (spc,constrOps) = addSortConstructorsToSpec spc in
    let spc = conformOpDecls spc in
    let spc = adjustAppl spc in
    spc

  def generateCSpec basespc spc =
    let spc = transformSpecForCodeGen basespc spc in
    generateCSpecFromTransformedSpec spc

  def generateCSpecFromTransformedSpec spc =
    let xcspc = emptyCSpec("") in
    generateCSpecFromTransformedSpecIncr xcspc spc

  def generateCSpecFromTransformedSpecIncr xcspc spc =
    let filter = (fn(_) -> true) in
    generateCSpecFromTransformedSpecIncrFilter xcspc spc filter

  def generateCSpecFromTransformedSpecIncrFilter xcspc spc filter =
    let useRefTypes = true in
    let constrOps = [] in
    %let _ = writeLine(printSpec spc) in
    let impunit = generateI2LCodeSpecFilter(spc,useRefTypes,constrOps,filter) in
    let cspec = generateC4ImpUnit(impunit, xcspc, useRefTypes) in
    cspec
    

  def generateCSpecFromTransformedSpecEnv spc =
    return (generateCSpecFromTransformedSpec spc)

  def printToFile(cspec,optFile) =
    let filename =
       case optFile of
	 | None          -> "cgenout.c"
	 | Some filename -> filename
    in
    let len = length(filename) in
    let basename = if substring(filename,len-2,len) = ".c" 
		     then substring(filename,0,len-2)
		   else filename
    in
    let _ = writeLine(";; writing generated code to "^basename^".[ch]...") in
    let cfilename = basename^".c" in
    let hfilename = basename^".h" in
    let (hdrcspc,cspc) = splitCSpec cspec in
    let cspec = addInclude(cspc,hfilename) in
    (printCSpecToFile(hdrcspc,hfilename);
     printCSpecToFile(cspec,cfilename))

  def printToFileEnv(cspec,optFile) =
    return (printToFile(cspec,optFile))

  def generateCCode(basespc, spc, _ (*fullspec*), optFile) =
    let _ = writeLine(";; bit-string special translation is turned "^
		      (if bitStringSpecial then "on" else "off"))
    in
    let cspec = generateCSpec basespc spc in
    printToFile(cspec,optFile)


  def sortToCType cspc spc srt =
    let ctxt1 = SpecsToI2L.defaultCgContext in
    let ctxt2 = I2LToC.defaultCgContext in
    let tyvars = [] in
    let i2lType = sort2type(ctxt1,spc,tyvars,srt) in
    c4Type(ctxt2,cspc,i2lType)

  def termToCExp cspc spc term =  
    let block = ([],[]) in
    termToCExpB cspc spc block term

  op termToCExpB: CSpec -> AnnSpec.Spec -> Block -> MS.Term -> (CSpec * Block * CExp)
  def termToCExpB cspc spc block term =  
    let ctxt1 = SpecsToI2L.defaultCgContext in
    let ctxt2 = I2LToC.defaultCgContext in
    let i2lExp = term2expression(ctxt1,spc,term) in
    c4Expression(ctxt2,cspc,block,i2lExp)

  def showQualifiedId(qid as Qualified(q,id)) =
    I2LToC.qname2id (q,id)

  def postProcessCSpec(cspc) =
    I2LToC.postProcessCSpec cspc


end-spec
