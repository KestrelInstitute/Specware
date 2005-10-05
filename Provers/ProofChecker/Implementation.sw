(* This is an executable version of spec Spec, i.e. an executable proof
checker. We obtain it by applying (1) the refinement of spec
OtherAbbreviations, (2) the refinement of spec Occurrences, (3) the
instantiation of primitive names, and (4) the library refinement of finite
structures as lists.

The order is important: if, for example, we substituted (4) first, then we
would be unable to substitute (1) or (2) or (3), because the spec resulting
after substituting (4) would contain not FiniteStructures, but its refined
version FiniteStructuresAsLists, and so the domain specs of (1) or (2) or (3)
would not be a subspec of the spec resulting after substituting (4).

For the same reason, we cannot just apply the refinements (1), (2), and (4) to
spec Spec (which would be the natural thing to do, intuitively). *)

MetaslangProofChecker qualifying spec

  import CheckerAndOtherAbbreviations
         [OtherAbbreviations_Refinement]
         [Occurrences_Refinement]
         [Primitives_Instantiation]
         [/Library/General/FiniteStructuresAsListsMorphism]

endspec
