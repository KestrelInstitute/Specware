Winner = spec
 type Nats  = List Nat
 type Bogus = | Nil | Other
 def f : Nats  = []
 def g : Nats  = Nil
 def h : Nats  = [33]
 def a : Bogus = Nil
 def b : Bogus = Other
endspec

Loser = spec
 type Nats  = List Nat
 type Bogus = | Nil | Other
 def loser : Bogus = []
endspec

Loser2 = spec
 type Nats  = List Nat
 type Bogus = | Nil | Other
 def loser = []
endspec
