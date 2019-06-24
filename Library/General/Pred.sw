(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Pred qualifying spec  %% "Predicate" is already the name of an Isabelle theory?

type Predicate a = a -> Bool

%% Lift negation to predicates:
op [a] ~~ (p:Predicate a) : Predicate a = fn x:a -> ~ (p x)

proof Isa Thy_Morphism
  Pred.~~ -> -
end-proof


end-spec
