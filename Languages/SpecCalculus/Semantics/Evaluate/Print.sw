SpecCalc qualifying spec {
  import Signature 

 def SpecCalc.evaluatePrint term = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base")
                     (SpecPath_Relative {path = ["Library","Base"],
                                         hashSuffix = None});
     (case value of
       | Spec spc -> print (printSpec (subtractSpec spc baseSpec))
       | Morph morph -> print (ppFormat (ppMorphism morph))
       | Diag dgm -> print
           (ppFormat
              (ppDiagram
                 (mapDiagram dgm (fn o -> subtractSpec o baseSpec) (fn a -> a))))
       | InProcess -> print "Not value!");
     return (value,timeStamp,depURIs)
   }
}
