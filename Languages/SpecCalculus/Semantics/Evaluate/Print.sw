SpecCalc qualifying spec {
  import Signature 
  import URI/Utilities

 def SpecCalc.evaluatePrint term = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
     baseURI <- pathToRelativeURI "/Library/Base";
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base") baseURI;
     (case value of
       | Spec  spc   -> print (printSpec (subtractSpec spc baseSpec))
       | Morph morph -> print (ppFormat (ppMorphism morph))
       | Diag  dgm   ->
           print (ppFormat (ppDiagram
                              (mapDiagram dgm 
                                          (fn obj -> subtractSpec obj baseSpec) 
                                          (fn arr -> arr))))
       | Colimit col -> print (ppFormat  (ppColimit col))
       | InProcess -> print "No value!");
     return (value,timeStamp,depURIs)
   }
}
