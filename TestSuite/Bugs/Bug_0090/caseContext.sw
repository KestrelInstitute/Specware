S = spec

  op f : fa(a) List a -> Nat
  def f l = case l of
              | Nil -> 0
              | _ -> 100 div length l

endspec


O = obligations S
