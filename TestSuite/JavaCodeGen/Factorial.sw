spec

  op fact : {i : Integer | i >= 0} -> Integer

  def fact(i) = if i = 0 then 1
                else i * (fact(i-1))

endspec
