%%% 
%%% 
%%% Proof obligations for quotient pattern are not generated
%%% 
%%% The op f in the attached file is not well-defined, because 
%%% its result depends on the choice y of the element of the 
%%% equivalence class x.
%%% 
%%% However, showing the obligations reveals that Specware 
%%% generated no proof obligation that the result of f does
%%%  not depend on the choice y.
%%% 
%%% (Also note that one of the generated proof obligations 
%%%  for f references an unbound variable X, instead of a 
%%%  universally quantified x.)
%%% 

S =
spec

  op eq_mod10 : Nat * Nat -> Bool
  def eq_mod10(n1,n2) = (n1 rem 10 = n2 rem 10)

  type Q = Nat / eq_mod10

  op f : Q -> Nat
  def f x =
    let quotient[Q] y = x in y+1

  op g : Q -> Nat
  def g x =
    choose[Q] (fn y -> y+1) x

  op f2 : Q -> List Nat
  def f2 x =
    let quotient[Q] y = x in [y+1]

  op g2 : Q -> List Nat
  def g2 x =
    choose[Q] (fn y -> [y+1]) x

endspec

O = obligations S

