spec
  type Injection1(a, b) = ((a -> b) | Functions.injective?)
    % was 
    %  type T = ((| Foo | Fum) | truep)
    %  type T1 = {x: (| Foo | Fum) | true}
    % but sum types are now only legal at top level
  type T0 = | Foo | Fum
  type T  = (T0 | truep)  
  type T1 = {x: T0 | true}
  type T2 = ((T * T1) | truep)

 op truep: [a] a -> Boolean
 axiom List.induction1 is [a]
    fa(p : List(a) -> Boolean) 
     p([]) 
     && (fa(x : a, l : List(a)) 
          (p l => p(Cons(x, l)) => (fa(l : List(a)) p l)))

endspec
