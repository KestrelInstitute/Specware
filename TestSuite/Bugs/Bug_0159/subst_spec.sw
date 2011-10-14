%% This is a moderately complicated test of spec substitution
%% The subsitution M applies to an A that is hidden inside the import of A2.
%% Also, A and B (the domain and codomain of M) both import misc specs, as does C and A2.

S = spec
     op foo : List Nat -> List Bool
     def foo nats =
       map (fn(n:Nat) -> if n=0 then false else true) nats
    endspec

A = spec
     import S
     type A
    end-spec

T = spec
     op baz : List Nat -> List Bool
     def baz nats =
       map (fn(n:Nat) -> if n=0 then false else true) nats
    endspec

B = spec
     import S
     type B 
     import T
    end-spec

M = morphism A -> B {A +-> B}

Z = spec
     type Z 
    end-spec

A2 = spec
     type A1
     import A
     import Z
     type A2
    end-spec

C = spec
     import A2
     type W 
     type Y 
     op bar : A -> A
    end-spec


subst_spec = C[M]

