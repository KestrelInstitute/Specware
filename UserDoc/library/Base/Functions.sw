Functions qualifying spec 
  import PrimitiveSorts

  op id : fa (A) A -> A
  op o infixl 24 : fa (A,B,C) (B -> C) * (A -> B) -> A -> C

  def id x = x
  def o (f1,f2) x = f1(f2 x)

endspec
