Aa = Aa qualifying spec
  def q = 456
endspec

aA = aA qualifying spec
  def q = 123
endspec

C = spec
  import Aa
  import aA
  def result_0047 = aA.q
endspec
