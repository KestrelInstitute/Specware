A = spec def fubaz = 12345 endspec

D = diagram { X +-> A, Y +-> A }

C = colimit D

E = spec import C  def f x = x + 1 endspec