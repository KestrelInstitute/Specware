SATFMI = SATFM qualifying spec
  import SATDPSig
  import FourierMotzkinGeneric

  type SAT.Formula = Ineq

  def SAT.isDecidable?(f) =
    isIneq?(f)

  def SAT.DPFalse = falseIneq

  def SAT.DPRefute?(fs) =
    case FMRefute?(fs) of
      | None -> Proved
      | Some ce -> CounterExample ce

endspec

SATWithFMMorph = morphism SATDPSig -> SATFMI {}

SATFMGeneric = SATGeneric[SATWithFMMorph]


