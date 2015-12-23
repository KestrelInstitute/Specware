(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SATFMI = SATFM qualifying spec
  import SATDPSig
  import DPGen/FourierMotzkinGeneric

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


