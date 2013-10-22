aspec = spec 
  type AA = Int * Int
  op switch: AA -> AA
  def switch (a1,a2) = (a2,a1)
  conjecture doubleswitchidentity is fa(i,j:Int) switch (switch(i,j)) = (i,j) 
%  conjecture doubleswitchidentity is fa (x:AA) switch (switch (x, 0), 0) = x 
endspec

aspecobs = obligations aspec

(*
:show test3#aspecobs

spec  
 import aspec
 import /Library/Base/WFO
 type AA = Int * Int
 op switch : AA -> AA
 def switch (a1, a2) = (a2, a1)
 op WFO.wfo : fa(a) (a * a -> Bool) -> Bool
 def WFO.wfo pred = 
     fa(p : a -> Bool) 
      ex(y : a) p y => ex(y : a) (p y && fa(x : a) (p x => ~(pred(x, y))))
 conjecture doubleswitchidentity is 
    fa(i : Int, j : Int) switch(switch(i, j)) = (i, j)
endspec

*)

p1 = prove doubleswitchidentity in aspec using switch_def, AA_def%, AA_ex 
options "(use-paramodulation t) (assert-supported t)"
