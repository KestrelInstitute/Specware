OpDef = spec
 op f : Nat
 def f = 3
endspec

DefOp = spec
 def f = 3
 op f : Nat
endspec

DefDef = spec
 def f = 3
 def f = 3
endspec

OpOp = spec
 op f : Nat
 op f : Nat
endspec

OpDefOp = spec
 op f : Nat
 def f = 3
 op f : Nat
endspec

OpDefDef = spec
 op f : Nat
 def f = 3
 def f = 3
endspec

Mixed = spec
 op f : String
 def f = true
 op f : Boolean
endspec



