A = spec
  type Counter
  op reset: Counter
  op tick : Counter -> Counter
  axiom Effect is fa (c : Counter) ~(tick c = c)
endspec

B = spec
  def reset : Int = 0  % default type would be Nat
  def tick c = c+1         % default type is Int -> Int
endspec

M = morphism A -> B {Counter +-> Int}

AA = spec
  import A
  type Interval = {start: Counter, stop: Counter}
  op  isEmptyInterval? : Interval -> Bool
  def isEmptyInterval? {start = x, stop = y} = (x = y)
endspec

BB = AA [M]
