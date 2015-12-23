(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Abstraction of Spec Calculus

This is an unfortunate (and perhaps unnecessary) mutual dependency
between specs in this directory and those in the directory for the spec
calculus. The SpecCalculus/AbstractSyntax/Types imports PosSpec. PosSpec
imports AnnSpec and AnnSpec needs the type SpecCalc.Term to record import
information. Similarly, the pretty printer for specs must pretty print
the spec calculus terms that are imported to that spec.

In this spec, we abstract the signature for the types and ops from
the spec calculus that are needed by local specs and thereby break
the recursion.
*)

spec
 type SpecCalc.Term a

 op SpecCalc.showTerm : [a] SpecCalc.Term a -> String

 op sameSCTerm? : [a] SpecCalc.Term a * SpecCalc.Term a -> Bool

end-spec
