SpecCalc qualifying spec {
  import Signature 
  import /Languages/MetaSlang/Specs/Elaborate/PosSpecToSpec

  def SpecCalc.evaluatePrint term = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base")
                     (SpecPath_Relative {path = ["Library","Base"],
                                         hashSuffix = None});
     (Spec pslBase,_,_) <- SpecCalc.evaluateURI (Internal "PSpec base")
                     (SpecPath_Relative {path = ["Library","PSL","Base"],
                                         hashSuffix = None});
     (case value of
       | Spec spc -> print (printSpec (subtractSpec spc baseSpec))
       | Morph morph -> print (ppFormat (ppMorphism morph))
       | Diag dgm -> print
           (ppFormat
              (ppDiagram
                 (mapDiagram dgm (fn o -> subtractSpec o baseSpec) (fn a -> a))))
       % The next is a hack to get around the two sorts of spec stuff.
       | PSpec pSpec -> 
           let fixPSpec = {
             staticSpec = convertPosSpecToSpec pSpec.staticSpec,
             dynamicSpec = convertPosSpecToSpec pSpec.dynamicSpec,
             procedures = pSpec.procedures
           } in
           print (ppFormat (ppPSpecLess fixPSpec pslBase))
       | InProcess -> print "No value!");
     return (value,timeStamp,depURIs)
   }
}
