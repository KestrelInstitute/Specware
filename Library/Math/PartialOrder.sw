spec

 type A
 op <= infixl 20 : A * A -> Boolean

 axiom reflexive_le is
    fa(a:A) a<=a

 axiom transitive_le is
    fa(a:A,b:A,c:A)(a<=b && b<=c => c<=a)

 axiom antisymmetric_le is
    fa(a:A,b:A)(a<=b && b<=a => a=b)

 op monotone: (A->A) -> Boolean
 axiom def_of_monotone is
   fa(a1:A,a2:A,f:A->A)(a1<=a2 => f(a1)<=f(a2))

end-spec