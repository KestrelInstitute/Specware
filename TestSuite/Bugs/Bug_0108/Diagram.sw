R = spec
 type A
end

S = spec
 type B
end

T = spec
 type C
end

M = morphism R -> S {A +-> B}
N = morphism R -> T {A +-> C}

D = diagram {a : x -> y +-> M, b : x -> z +-> N}

C = colimit D


