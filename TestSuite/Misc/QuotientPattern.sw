spec
   sort Bag a = (List a) / perm?
   op perm?: fa(a) List a  * List a -> Boolean
   op bag_fold : fa(a,b) b ->
                         {f : a * b -> b |
                          fa(x,y,z) f(x,f(y,z)) = f(y,f(x,z))} ->
                         Bag a ->
                         b

   def bag_fold c f (quotient Bag l) = (foldl f c l)
endspec
(*
  
*)
