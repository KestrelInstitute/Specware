R = spec
 type A1
 type A2
 type A3
 op f : A1 * A2 -> A3
end

S = spec
 type B1
 type B2
 type B3
 op g : B1 * B2 -> B3
end

T = spec
 type C1
 type C2
 type C3
 op h : C1 * C2 -> C3
end

M = morphism R -> S {A1 +-> B1, A2 +-> B2, A3 +-> B3, f +-> g}
N = morphism R -> T {A1 +-> C1, A2 +-> C2, A3 +-> C3, f +-> h}

D = diagram {a : x -> y +-> M, b : x -> z +-> N}

% C = colimit D


