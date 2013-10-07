spec

  op gcd : {(n1,n2) : Int * Int | n1 > 0 && n2 > 0} -> Int

  def gcd(n1,n2) = if (n1 > n2) then gcd(n1-n2,n2)
              else if (n1 < n2) then gcd(n1,n2-n1)
              else  (* n1 = n2 *)    n1  % = n2

endspec
