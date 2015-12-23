(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

JoinSemilattice = spec

 import PartialOrder#PartialOrder
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

MeetSemilattice = spec

 import PartialOrder
 op meet: A*A->A

 axiom idempotent_Meet is
    fa(a:A) meet(a,a)=a

 axiom symmetric_RefinesTo is
    fa(a:A,b:A) meet(a,b) = meet(b,a)

 axiom meet_is_a_lower_bound is
    fa(a:A,b:A,c:A)(meet(a,b)=c => (c<=a && c<=b))

 axiom meet_is_greatest_lower_bound is
    fa(a:A,b:A,c:A)(c<=a && c<=b =>  c<=meet(a,b))

end-spec

(********** unfinished ************
MeetSemilattice2 = spec

 import translate PartialOrder {
 op meet: A*A->A

 axiom idempotent_Meet is
    fa(a:A) meet(a,a)=a

 axiom symmetric_RefinesTo is
    fa(a:A,b:A) meet(a,b) = meet(b,a)

 axiom meet_is_a_lower_bound is
    fa(a:A,b:A,c:A)(meet(a,b)=c => (c<=a && c<=b))

 axiom meet_is_greatest_lower_bound is
    fa(a:A,b:A,c:A)(c<=a && c<=b =>  c<=meet(a,b))

end-spec
*)

%----------------------------------------------------

BoundedJoinSemilattice = spec

 import JoinSemilattice
 op bot: A

 axiom universal_lower_bound is  % lub of the empty set
    fa(a:A) bot <= a

end-spec

BoundedMeetSemilattice = spec

 import MeetSemilattice
 op top: A

 axiom universal_lower_bound is   % glb of the empty set
    fa(a:A) a <= top

end-spec
