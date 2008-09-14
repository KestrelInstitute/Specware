spec
   sort Bag a = (List a) / perm?
   op perm?: fa(a) List a  * List a -> Boolean
   op bag_fold : [a,b] b ->
                       {f : b * a -> b | fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)} ->
                       Bag a ->
                       b
   def bag_fold c f (quotient[Bag] l) = (foldl f c l)
endspec
