SpecCalc qualifying spec {
  import Signature 

 def SpecCalc.evaluatePrint term = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
     (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "base")
                                                 (SpecPath_Relative {path = ["Library","Base"],
								     hashSuffix = None});
     (case value of
       | Spec  spc   -> print (printSpec (subtractSpec spc baseSpec))
       | Morph morph -> print (ppFormat  (ppMorphism morph))
       | Diag  dgm   -> print (ppFormat  (ppDiagram
					  (mapDiagram dgm 
					              (fn obj -> subtractSpec obj baseSpec) 
						      (fn a -> a))))
       | Colimit col -> print (ppFormat  (ppColimit col))
       | InProcess -> print "No value!");
     return (value,timeStamp,depURIs)
   }
}
