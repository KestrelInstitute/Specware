aA = aA qualifying spec
  def q = 123
endspec

Aa = Aa qualifying spec
  def q = 456
endspec

C = spec
  import aA
  import Aa
  def low_high = aA.q
  def high_low = Aa.q
endspec
