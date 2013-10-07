spec

  op ho : (Int -> Int) -> Int
  def ho f = f 2

  op sqr : Int -> Int
  def sqr i = i * i

  op hoUser : Int -> Int
  def hoUser i =
    let i1 = ho(fn x -> x+1) in
    let i2 = ho sqr in
    let i3 = ho(fn y -> y-i) in
    i1 + i2 + i3

endspec
