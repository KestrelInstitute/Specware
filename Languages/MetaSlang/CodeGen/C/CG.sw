CG qualifying
spec
  import SpecsToI2L
  import I2LToC
  import /Languages/MetaSlang/CodeGen/CodeGenTransforms
  import /Languages/MetaSlang/Transformations/RemoveCurrying
  import /Languages/MetaSlang/Transformations/LambdaLift


% --------------------------------------------------------------------------------

op builtinSortOp: QualifiedId -> Boolean
def builtinSortOp(qid) =
  let Qualified(q,i) = qid in
  %(q="Nat" & (i="Nat" or i="PosNat" or i="toString" or i="natToString" or i="show" or i="stringToNat"))
  %or
  (q="Integer" & (i="Integer" or i="NonZeroInteger" or i="+" or i="-" or i="*" or i="div" or i="rem" or i="<=" or
		  i=">" or i=">=" or i="toString" or i="intToString" or i="show" or i="stringToInt"))
  or
  (q="Boolean" & (i="Boolean" or i="true" or i="false" or i="~" or i="&" or i="or" or
		  i="=>" or i="<=>" or i="~="))
  or
  (q="Char" & (i="Char" or i="chr" or i="isUpperCase" or i="isLowerCase" or i="isAlpha" or
	       i="isNum" or i="isAlphaNum" or i="isAscii" or i="toUpperCase" or i="toLowerCase"))
  or
  (q="String" & (i="String" or i="writeLine" or i="toScreen" or i="concat" or i="++" or
		 i="^" or i="newline" or i="length" or i="substring"))


% --------------------------------------------------------------------------------

  op generateCCode: AnnSpec.Spec * AnnSpec.Spec * AnnSpec.Spec * Option(String) -> ()
  def generateCCode(basespc, spc, _ (*fullspec*), optFile) =
    let _ = writeLine(";; Generating C Code....") in
    let useRefTypes = true in
    let spc = addMissingFromBase(basespc,spc,builtinSortOp) in
    let spc = removeCurrying spc in
    %let _ = writeLine(printSpec spc) in
    %let _ = writeLine("---------------------------------") in
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
