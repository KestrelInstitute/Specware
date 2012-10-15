spec

 type A
 op POle: A*A->Boolean

 axiom reflexive_POle is
    fa(a:A) POle(a,a)

 axiom transitive_POle is
    fa(a:A,b:A,c:A)(POle(a,b) && POle(b,c) => POle(a,c))

 axiom antisymmetric_POle is
    fa(a:A,b:A)(POle(a,b) && POle(b,a) => a=b)

 op monotone: (A->A) -> Boolean
 axiom def_of_monotone is
   fa(a1:A,a2:A,f:A->A)(POle(a1,a2) => POle(f a1,f a2))

end-spec