AnnSpec qualifying
spec
 import QualifierMap
 import /Library/Legacy/DataStructures/StringMapSplay
 import SpecCalc qualifying
    (translate (translate /Library/Legacy/DataStructures/Monadic/SplayMap
     by {Monad._ +-> SpecCalc._})
     by {SpecCalc.Monad +-> SpecCalc.Env})
 sort AQualifierMap b  = StringMap (StringMap b)    
 def foldriAQualifierMap      = StringMap.foldriDouble  % f ini qm
 def emptyAQualifierMap       = StringMap.empty         % 
 def findAQualifierMap        = StringMap.find2         % (m, x, y)
 def insertAQualifierMap      = StringMap.insert2       % (qm, x, y, v)
 def mapAQualifierMap         = StringMap.mapDouble     % f m
 def mapiAQualifierMap        = StringMap.mapiDouble    % f m
 def mapiPartialAQualifierMap = mapiPartialDouble
 def appAQualifierMap         = StringMap.appDouble     % f m
 def appiAQualifierMap        = StringMap.appiDouble    % f m
 def qualifiers m = 
   StringMap.foldri (fn (q, _, quals) -> cons(q,quals)) [] m
 def qualifierIds m = 
   StringMap.foldriDouble (fn(_,id,_,quals) -> cons(id,quals)) [] m

 def foldOverQualifierMap f e m = foldDoubleMap f e m

endspec
