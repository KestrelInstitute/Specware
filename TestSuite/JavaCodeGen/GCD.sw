spec

  op gcd : {(n1,n2) : Integer * Integer | n1 > 0 & n2 > 0} -> Integer

  def gcd(n1,n2) = if (n1 > n2) then gcd(n1-n2,n2)
              else if (n1 < n2) then gcd(n1,n2-n1)
              else  (* n1 = n2 *)    n1  % = n2

endspec
