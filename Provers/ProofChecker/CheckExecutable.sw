(* We make spec `Check' executable by substituting (1) the refinement
`SyntaxWithCoreOpsRefined' of `SyntaxWithCoreOps', (2) the instantiation of
primitives as strings, and (3) the library refinement of finite structures as
lists. The order is important: if, for example, we substituted (3) first, then
we would be unable to substitute (1) or (2), because the spec resulting after
substituting (3) would contain not `FiniteStructures', but its refined version
`FiniteStructuresAsLists', and so the domain specs of (1) and (2) would not be
a subspec of the spec resulting after substituting (3). *)

Check[SyntaxWithCoreOpsRefinedMorphism]
     [PrimitivesAsStringsMorphism]
     [morphism /Library/General/FiniteStructures ->
               /Library/General/FiniteStructuresAsLists {}]
