X1 = spec 
  sort X1  = Integer * Integer
  op  makeX : Integer * Integer -> X1
  def makeX(i,j) = (i, j)
  conjecture twoMakesMakeAMatch1 is 
      fa(i1,i2,j1,j2) 
      makeX(i1, j1) = makeX (i2, j2) => 
      ( i1 = i2 & j1 = j2)

  conjecture twoMakesMakeAMatch2 is 
      fa(i1,i2,j1,j2) 
      ( i1 = i2 & j1 = j2) =>
      makeX(i1, j1) = makeX (i2, j2)
endspec 

O1 = obligations X1

P1 = prove twoMakesMakeAMatch1 in O1 

P2 = prove twoMakesMakeAMatch2 in O1 
