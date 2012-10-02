
Dom = spec
type T
op f : T
endspec

Cod_1_1 = Q qualifying spec
type T
op f : T
endspec

M_1_1 = morphism Dom -> Cod_1_1 {}  % should succeed

Cod_2_1 = Q qualifying spec
type T
op f : T
type Z.T
endspec

M_2_1 = morphism Dom -> Cod_2_1 {} % should fail - type T is ambiguous

Cod_1_2 = Q qualifying spec
type T
op f : T
op Z.f : T
endspec

M_1_2 = morphism Dom -> Cod_1_2 {} % should fail - op f is ambiguous

Cod_2_2 = Q qualifying spec
type T
op f : T
type Z.T
op Z.f : T
endspec

M_2_2 = morphism Dom -> Cod_2_2 {} % should fail - type T and op f are ambiguous
