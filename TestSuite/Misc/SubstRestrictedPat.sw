A=
spec

  def f x =
    let b = hd x in
    case x of
      | a::_ | a = b -> a
      | _ -> 0

  def v = f [3]

endspec

B=
spec

  def g x =
    let p = true in
    case x of
      | a::_ | p -> a
      | _ -> 0

endspec
