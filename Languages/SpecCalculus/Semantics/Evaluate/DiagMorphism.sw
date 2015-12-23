(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecCalc qualifying spec {
  import Signature

  def SpecCalc.evaluateDiagMorph (domTerm,codTerm,morphRules) = {
      domValueInfo <- SpecCalc.evaluateTermInfo domTerm;
      codValueInfo <- SpecCalc.evaluateTermInfo codTerm;
      let (domValue,_,_) = domValueInfo in
      let (codValue,_,_) = codValueInfo in
      raise (Unsupported ((positionOf domTerm),
                          "diagram morphisms not available yet\n" 
			  ^ "Dom diagram  = \n" 
			  ^ showValue domValue 
			  ^ "\n"
			  ^ "Cod diagram  = \n" 
			  ^ showValue codValue 
			  ^ "\n"
			  ^ (Nat.show (List.length morphRules)) 
			  ^ " diagram-morphism rules \n"))
    }
}

