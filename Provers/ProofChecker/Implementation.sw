(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* This is an executable version of spec Spec, i.e. an executable proof
checker. We obtain it by applying (1) the refinement of spec
OtherAbbreviations, (2) the instantiation of primitive names, and (3) the
library refinement of finite structures as lists.

The order is important: if, for example, we substituted (3) first, then we
would be unable to substitute (1) or (2), because the spec resulting after
substituting (3) would contain not FiniteStructures, but its refined version
FiniteStructuresAsLists, and so the domain specs of (1) or (2) would not be
subspecs of the spec resulting after substituting (3).

For the same reason, we cannot just apply the refinements (1) and (2) to spec
Spec (which would be the natural thing to do, intuitively). *)

MetaslangProofChecker qualifying spec

  import CheckerAndOtherAbbreviations
         [OtherAbbreviations_Refinement]
         [Primitives_Instantiation]
         [/Library/General/FiniteMapAsListMorphism]

endspec
