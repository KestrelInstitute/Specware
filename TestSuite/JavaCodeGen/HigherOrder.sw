spec

  op ho : (Integer -> Integer) -> Integer
  def ho f = f 2

  op sqr : Integer -> Integer
  def sqr i = i * i

  op hoUser : Integer -> Integer
  def hoUser i =
    let i1 = ho(fn x -> x+1) in
    let i2 = ho sqr in
    let i3 = ho(fn y -> y-i) in
    i1 + i2 + i3

endspec
