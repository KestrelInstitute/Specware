spec

%% NOTE: Keep these in sync with the examples in metaslang.rst !

%% Examples from type-declarations section:

type Date
type Array a
type Map(a, b)

%% Examples from type-definitions section:

   op [a,b] key_uniq? : Array (a * b) -> Bool

   type MyFun = Nat -> Nat
   type MyProd = Nat * Nat
   type MyProd2 = MyProd
   type Date = {year : Nat, month : Nat, day : Nat}
   type Array a = List a
   type PosNat = (Nat | positive?)
   type PosNat2 = {x:Nat | positive? x}
   type Map(a, b) = (Array (a * b) | key_uniq?)

%   type MyBool = Bool
%   type MyWrapper a = a

   type Tree         a = | T.Leaf a | T.Fork (Tree a * Tree a)
   type Bush         a = | B.Leaf a | B.Fork (Tree a * Tree a)

% Removed this one, since we don't want to advertise this syntax:
%   type {Bush,Shrub} a = | Leaf a | Fork (Tree a * Tree a)

   op rem (x:Nat, y:Nat) infixl 26 : Nat
   type Z3 =  Nat / (fn (m, n) -> m rem 3 = n rem 3)

   type Stack a =
     | Empty
     | Push {top : a, pop : Stack a}

   op [a] hasBottom? (s : Stack a) : Bool =
     case s of
        | Empty -> true
        | Push {top, pop = rest} -> hasBottom? rest


end-spec