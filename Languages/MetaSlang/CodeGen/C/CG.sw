CG qualifying
spec
  import SpecsToI2L
  import I2LToC
  import /Languages/MetaSlang/CodeGen/CodeGenTransforms
  import /Languages/MetaSlang/Transformations/RemoveCurrying
  import /Languages/MetaSlang/Transformations/LambdaLift



% --------------------------------------------------------------------------------

  op generateCCode: AnnSpec.Spec * AnnSpec.Spec * AnnSpec.Spec * Option(String) -> ()
  def generateCCode(basespc, spc, _ (*fullspec*), optFile) =
    %let _ = showSorts spc in
    let _ = writeLine(";; Generating C Code....") in
    %let _ = writeLine(printSpec spc) in
    %let _ = writeLine("---------------------------------") in
    let useRefTypes = true in
    let spc = addMissingFromBase(basespc,spc,builtinSortOp) in
    let spc = removeCurrying spc in
    let spc = lambdaToInner spc in
    %let _ = writeLine(printSpec spc) in
    let spc = poly2mono(spc,false) in
    %let _ = writeLine(printSpec spc) in
    let spc = lambdaLift spc in
    let (spc,constrOps) = addSortConstructorsToSpec spc in
    let spc = conformOpDecls spc in
    let spc = adjustAppl spc in
    %let _ = writeLine(printSpec spc) in
    let impunit = generateI2LCodeSpec(spc, spc, useRefTypes, constrOps) in
    let cspec = generateC4ImpUnit(impunit, useRefTypes) in
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


end-spec
