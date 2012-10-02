%% This is a moderately complicated test of spec substitution
%% The subsitution M applies to an A that is hidden inside the import of A2.
%% Also, A and B (the domain and codomain of M) both import misc specs, as does C and A2.

S = spec
     op foo : List Nat -> List Bool
     def foo nats =
       map (fn(n:Nat) -> if n=0 then false else true) nats
    endspec

B = spec
     import S
     type B
    end-spec

C = spec
     type C
    end-spec

A = spec
     type A
     import B
     import C
     type D
    end-spec

E = spec
     import A
     type X
     type Y 
     op bar : A -> A
    end-spec

qualify_spec = Q qualifying E 

