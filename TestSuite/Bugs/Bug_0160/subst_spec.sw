
A = spec
     type A
    end-spec

B = spec
     op foo (nats: List Nat): List Boolean =
       map (fn(n:Nat) -> if n=0 then false else true) nats
     type B 
    end-spec

M = morphism A -> B {A +-> B}

C = spec
     import A
     op foo : A -> A
    end-spec

subst_spec = C[M]

