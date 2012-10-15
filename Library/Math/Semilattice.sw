spec

 import PartialOrder
 op join: A*A->A

 axiom idempotent_Join is
    fa(a:A) join(a,a)=a

 axiom symmetric_RefinesTo is
    fa(a:A,b:A) join(a,b) = join(b,a)

 axiom join_is_an_upper_bound is
    fa(a:A,b:A,c:A)(join(a,b)=c => (a<=c && b<=c))

 axiom join_is_least_upper_bound is
    fa(a:A,b:A,c:A)(a<=c && b<=c =>  join(a,b)<=c)

end-spec