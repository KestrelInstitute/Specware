AnnSpec qualifying
spec
 import QualifierMap
 import /Library/Structures/Data/Maps/SimpleAsAlist
 sort AQualifierMap b  = Map(String * String,b)   
 def foldriAQualifierMap f ini qm =
   foldi (fn((q,id),v,r) -> f(q,id,v,r)) ini qm
 def emptyAQualifierMap  = emptyMap         % 
 def findAQualifierMap(m, x, y) = apply m (x,y)
 def insertAQualifierMap(qm, x, y, v) = update qm (x,y) v
 def mapAQualifierMap = map 
 def mapiAQualifierMap f m = mapi (fn ((q,id),v) -> f(q,id,v)) m
 def appAQualifierMap = app
 def qualifiers m =
    foldi (fn((qname,_),_,quals) -> cons(qname,quals)) [] m
 def qualifierIds m = 
    foldi (fn((_,id),_,quals) -> cons(id,quals)) [] m

 def foldOverQualifierMap f e m =
   case m of
     | [] -> return e
     | ((x,y),v) :: r -> {result <- f(x,y,v,e);
			  foldOverQualifierMap f result r}
endspec