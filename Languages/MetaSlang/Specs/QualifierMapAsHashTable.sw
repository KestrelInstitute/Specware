AnnSpec qualifying
spec
 import QualifierMap
 import /Library/Structures/Data/Maps/SimpleAsHarray
 sort AQualifierMap b  = Map(String * String,b)   
 def foldriAQualifierMap f ini qm =
   foldi (fn((q,id),v,r) -> f(q,id,v,r)) ini qm
 def emptyAQualifierMap  = Map.emptyMap         % 
 def findAQualifierMap(m, x, y) = apply m (x,y)
 def insertAQualifierMap(qm, x, y, v) = update qm (x,y) v
 def mapAQualifierMap = map 
 def mapiAQualifierMap f m = mapi (fn ((q,id),v) -> f(q,id,v)) m
 def appAQualifierMap  = app
 def appiAQualifierMap = appi
 def qualifiers m =
    foldi (fn((qname,_),_,quals) -> if member(qname,quals)
	                             then quals
				     else cons(qname,quals))
      [] m
 def qualifierIds m = 
    foldi (fn((_,id),_,ids) -> if member(id,ids)
	                          then ids
				 else cons(id,ids))
      [] m

 %% Temporary to get stuff working
 op foldL: fa(a,b) (a * b -> SpecCalc.Env b) -> b -> List a -> SpecCalc.Env b
 def foldL f e l =
   case l of
     | [] -> return e
     | x :: r -> {result <- f(x,e);
		  foldL f result r}
     

 def foldOverQualifierMap f e m =
   foldL (fn (x as (q,id),r) -> f(q,id,eval m x,r))
     e (Map.domainToList m)

endspec
