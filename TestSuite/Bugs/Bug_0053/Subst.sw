A = spec
  sort Counter
  op reset: Counter
  op tick : Counter -> Counter
  axiom Effect is
    fa (c : Counter) ~(tick c = c)
endspec

B = spec
  def reset = 0
  def tick c = c+1
endspec

M = morphism A -> B {Counter +-> Nat}

AA = spec
  import A
  sort Interval = {start: Counter, stop: Counter}
  op isEmptyInterval? : Interval -> Boolean
  def isEmptyInterval? {start = x, stop = y} = (x = y)
endspec

BB = AA [M]
