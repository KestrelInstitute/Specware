Foo = spec type Foo x = List (x * x) endspec

AA = spec type A  endspec

BB = spec import Foo type B = Foo Nat endspec

CC = spec type C = List (Nat * Nat) endspec

MM = morphism AA -> BB {A +-> B}

NN = morphism AA -> CC {A +-> C}

DD = diagram {A +-> AA, 
	      B +-> BB, 
	      C +-> CC, 
	      M : A -> B +-> MM,
	      N : A -> C +-> NN}

XX = colimit DD
