%% This is a moderately complicated test of spec substitution
%% The subsitution M applies to an A that is hidden inside the import of A2.
%% Also, A and B (the domain and codomain of M) both import misc specs, as does C and A2.

S = spec
     op foo : List Nat -> List Boolean
     def foo nats =
       map (fn(n:Nat) -> if n=0 then false else true) nats
    endspec

B = spec
     import S
     sort B
    end-spec

C = spec
     sort C
    end-spec

A = spec
     type A
     import B
     import C
     type D
    end-spec

E = spec
     import A
     sort X
     sort Y 
     op bar : A -> A
    end-spec

XX = translate E by {A +-> A2}
trans_spec = spec
              type AA
              import XX
              type ZZ
             endspec

