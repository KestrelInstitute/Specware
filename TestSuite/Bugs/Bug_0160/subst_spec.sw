%% This is a moderately complicated test of spec substitution
%% The subsitution M applies to an A that is hidden inside the import of A2.
%% Also, A and B (the domain and codomain of M) both import misc specs, as does C and A2.

A = spec
     type A
    end-spec

B = spec
     op foo : List Nat -> List Boolean
     def foo nats =  map (fn(n:Nat) -> if n=0 then false else true) nats
     type B 
    end-spec

M = morphism A -> B {A +-> B}

C = spec
     import A
     op foo : A -> A
    end-spec

subst_spec = C[M]

