
A = X qualifying spec

 type FFF (x,y) = x -> y

 type HHH (a,b) = FFF(FFF(a,b), FFF(a,b))  
 op f : [a,b] FFF(FFF(a,b), FFF(a,b))  
 op g infixl 24 : [a,b,c] FFF(b,c) * FFF(a,b) -> FFF(a,c)
 op h infixl 24 : [a,b,c] (b -> c) * (a -> b) -> (a -> c)

endspec

B = X qualifying spec

 type GGG (x,y) = x -> y

 type HHH (a,b) = GGG(GGG(a,b), GGG(a,b))  
 op f : [a,b] GGG(GGG(a,b), GGG(a,b))  
 op g infixl 24 : [a,b,c] (b -> c) * (a -> b) -> (a -> c)
 op h infixl 24 : [a,b,c] GGG(b,c) * GGG(a,b) -> GGG(a,c)

endspec

C = X qualifying spec

 import A
 import B

endspec


