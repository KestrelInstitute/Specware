Script qualifying
spec
 import /Languages/SpecCalculus/Semantics/Monad

 op redundantErrorCorrecting (spc: Spec) (morphs: List(SCTerm * Morphism)) (tracing?: Bool): SpecCalc.Env(Spec * Bool) =
   return(spc, tracing?)

end-spec
