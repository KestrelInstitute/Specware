aspec = spec 
  sort AA = Integer * Integer
  op switch: AA -> AA
  def switch (a1,a2) = (a2,a1)
  conjecture doubleswitchidentity is fa(i,j:Integer) switch (switch(i,j)) = (i,j) 
%  conjecture doubleswitchidentity is fa (x:AA) switch (switch (x, 0), 0) = x 
endspec

aspecobs = obligations aspec

(*
:show test3#aspecobs

spec  
 import aspec
 import /Library/Base/WFO
 sort AA = Integer * Integer
 op switch : AA -> AA
 def switch (a1, a2) = (a2, a1)
 op WFO.wfo : fa(a) (a * a -> Boolean) -> Boolean
 def WFO.wfo pred = 
     fa(p : a -> Boolean) 
      ex(y : a) p y => ex(y : a) (p y & fa(x : a) (p x => ~(pred(x, y))))
 conjecture doubleswitchidentity is 
    fa(i : Integer, j : Integer) switch(switch(i, j)) = (i, j)
endspec

*)

p1 = prove doubleswitchidentity in aspec using switch_def, AA_def%, AA_ex 
options "(use-paramodulation t) (assert-supported t)"