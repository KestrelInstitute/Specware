SpecCalc qualifying spec {
  import Signature 

 def SpecCalc.evaluatePrint term = {
     (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
     print (showValue value);
     return (value,timeStamp,depURIs)
   }
}
