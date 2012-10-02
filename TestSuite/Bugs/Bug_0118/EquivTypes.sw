
A = X qualifying spec

 type FFF (x,y) = x -> y
 type HHH (a,b) = FFF(FFF(a,b), FFF(a,b))  

 op f : [a,b] FFF(FFF(a,b), FFF(a,b))  
 op g infixl 24 : [a,b,c] FFF(b,c) * FFF(a,b) -> FFF(a,c)
 op h infixl 24 : [a,b,c] (b -> c) * (a -> b) -> (a -> c)

 op foo : [a] a -> a
 def foo x = x

endspec

B = X qualifying spec

 type GGG (x,y) = x -> y
 type HHH (a,b) = GGG(GGG(a,b), GGG(a,b))  

 op f : [a,b] GGG(GGG(a,b), GGG(a,b))  
 op g infixl 24 : [a,b,c] (b -> c) * (a -> b) -> (a -> c)
 op h infixl 24 : [a,b,c] GGG(b,c) * GGG(a,b) -> GGG(a,c)

 op id : [a] GGG(a,a)
 def id x = x

endspec

C = X qualifying spec

  type JJJ(a,b) = a -> b

  op id : [a] JJJ(a,a)
  def id x = x

endspec

D = spec

 import A
 import B
 import C

endspec



