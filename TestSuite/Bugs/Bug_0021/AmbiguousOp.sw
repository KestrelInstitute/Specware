A = spec 
 sort a
 sort b
 op c: a -> b
end-spec

B = spec
 sort e
end-spec

C = spec 
 sort a
 sort b
 op c: a -> b
end-spec

D = colimit diagram {
    m : B -> A +-> morphism B -> A {e +-> a},
    n : B -> C +-> morphism B -> C {e +-> b}
}

E = spec
 import D
 op f: a -> b
end-spec