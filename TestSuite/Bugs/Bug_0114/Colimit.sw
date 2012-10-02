
R = spec

 type X
 op f : X

endspec

S = spec

 type Y
 op g : Y

endspec

T = spec

 type Z
 op h : Z

endspec

D = diagram
  {
   a : r -> s +-> morphism R -> S {X +-> Y, f +-> g},
   b : r -> t +-> morphism R -> T {X +-> Z, f +-> h}
  }

C = colimit D

