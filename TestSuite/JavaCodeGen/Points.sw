spec

  type Point = {x : Int,
                y : Int}

  op add : Point * Point -> Point
  def add(p1,p2) = {x = p1.x + p2.x,
                    y = p1.y + p2.y}

  op abs : Int -> Int
  def abs(i) = if i < 0 then -i else i

  op square_distance : Point * Point -> Int
  def square_distance(p1,p2) =
      let delta_x = abs(p1.x-p2.x) in
      let delta_y = abs(p1.y-p2.y) in
      delta_x * delta_x + delta_y * delta_y

  op zero : Int
  def zero = 0

  op origin : Point
  def origin = {x = zero,
                y = zero}

endspec
