ThreeValues = spec 
  sort  Three
  op    nextmod3: Three -> Three
  axiom threedifferent is 
        fa(t)     ~(nextmod3 t = t)
endspec 

ThreeValuesDef = spec 
  sort Three      = | Z0 | Z1 | Z2
  op   nextmod3:  Three -> Three
  def  nextmod3 t = (case t of | Z0 -> Z1
                               | Z1 -> Z2
                               | Z2 -> Z0) 

  sort foo = | A | B (Integer * Integer)

%  axiom z0notz1 is ~(Z0 = Z1)
%  axiom z0notz2 is ~(Z0 = Z2)
%  axiom z1notz2 is ~(Z1 = Z2)

%  axiom allZ is fa (Three: Three) Three = Z0 or Three = Z1 or Three = Z2

%  conjecture nextmod3z0 is 
%        ~(nextmod3 Z0 = Z0)
%  conjecture nextmod3z1 is 
%        ~(nextmod3 Z1 = Z1)
%  conjecture nextmod3z2 is 
%        ~(nextmod3 Z2 = Z2)
%  conjecture nextmod3imp is 
%        (~(nextmod3 Z0 = Z0) &
%         ~(nextmod3 Z1 = Z1) &
%         ~(nextmod3 Z2 = Z2))
%        =>
%        (fa(t) ~(nextmod3 t = t))

  theorem threedifferent is 
        fa(t)     ~(nextmod3 t = t)

endspec

ThreeM   = morphism ThreeValues -> ThreeValuesDef {}

ThreeObs = obligations ThreeM

ThreeP   = prove threedifferent in ThreeValuesDef using nextmod3_def, Three_def%, allZ
           %z0notz1, z0notz2, z1notz2, allZ
           %nextmod3z0, nextmod3z1, nextmod3z2
           options "(assert-supported t) (use-paramodulation t)"