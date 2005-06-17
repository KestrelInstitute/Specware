A = spec
  type Counter
  op reset: Counter
  op tick : Counter -> Counter
  axiom Effect is fa (c : Counter) ~(tick c = c)
endspec

B = spec
  def reset : Integer = 0  % default type would be Nat
  def tick c = c+1         % default type is Integer -> Integer
endspec

M = morphism A -> B {Counter +-> Integer}

AA = spec
  import A
  type Interval = {start: Counter, stop: Counter}
  op  isEmptyInterval? : Interval -> Boolean
  def isEmptyInterval? {start = x, stop = y} = (x = y)
endspec

BB = AA [M]
