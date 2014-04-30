Pred qualifying spec  %% "Predicate" is already the name of an Isabelle theory?

%% TODO: Have the set library import this!  Then add this to All.sw

type Predicate a = a -> Bool

%% Lift negation to predicates:
op [a] ~~ (p:Predicate a) : Predicate a = fn x:a -> ~ (p x)

end-spec
