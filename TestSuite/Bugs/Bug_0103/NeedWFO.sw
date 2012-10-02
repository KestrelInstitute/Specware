S = spec

  op f : fa(a) {(l,i) : List a * Nat | i < length l} -> a

  def f(hd::tl,i) =
    if i = 0 then 
      hd
    else 
      f(Cons(hd,tl),i)    % WRONG

endspec


O  = print obligations S

P  = prove f_Obligation_exhaustive  in O
%P0 = prove f_Obligation0 in O
%P1 = prove f_Obligation1 in O


