spec

  op fact : {i : Int | i >= 0} -> Int

  def fact(i) = if i = 0 then 1
                else i * (fact(i-1))

endspec
