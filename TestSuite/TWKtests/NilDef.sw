Sets =  spec
  sort  E
  sort  Set E          = | MyNil | Insert E * Set E 
  op nil : Set E
  def nil = MyNil
  op xx  : Set E
  conjecture nildef is nil = MyNil
  conjecture xxdef  is xx  = MyNil
endspec