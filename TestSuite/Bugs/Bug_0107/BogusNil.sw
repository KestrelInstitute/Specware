spec
 type NotList a = | Nil | Cons (a * NotList a)
 def bogus_nil  : NotList Nat = Nil                                      %% Don't print as [] 
 def bogus_cons : NotList Nat = Cons (4, Cons (5, Cons (6, bogus_nil)))  %% Don't print as [5,6] 
 def true_nil   : List Nat  = []
 def true_cons  : List Nat  = [1,2,3]
endspec