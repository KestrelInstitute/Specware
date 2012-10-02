
R = spec type X endspec
S = spec type Y endspec
T = spec type Z endspec

D = diagram { 
	     a : p -> q +-> morphism R -> S {X +-> Y},
	     b : p -> r +-> morphism R -> T {X +-> Z}
	      }

C1 = colimit diagram { 
		      a : p -> q +-> morphism R -> S {X +-> Y},
		      b : p -> r +-> morphism R -> T {X +-> Z}
		       }

C2 = colimit D
