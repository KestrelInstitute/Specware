AnnSpec qualifying
spec
 import QualifierMap
 import /Library/Structures/Data/Maps/SimpleAsSTHarray
 sort AQualifierMap b  = STHMap.Map(String * String,b)   
 def foldriAQualifierMap f ini qm =
   foldi (fn((q,id),v,r) -> f(q,id,v,r)) ini qm
 def emptyAQualifierMap  = STHMap.emptyMap       % 
 def findAQualifierMap    (m, x, y)    = STHMap.apply  (m,  (x,y))
 def removeAQualifierMap  (m, x, y)    = STHMap.remove (m,  (x,y))
 def insertAQualifierMap (qm, x, y, v) = STHMap.update (qm, (x,y), v)
 def mapAQualifierMap = map 
 def mapiAQualifierMap f m = mapi (fn ((q,id),v) -> f(q,id,v)) m
 def mapiPartialAQualifierMap f m = mapiPartial (fn ((q,id),v) -> f(q,id,v)) m
 def appAQualifierMap  = app
 def appiAQualifierMap  f m = appi (fn ((q,id),v) -> f(q,id,v)) m
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

  op SpecCalc.return : fa (a) a -> SpecCalc.Env a
  op SpecCalc.monadBind : fa (a,b) (SpecCalc.Env a) * (a -> SpecCalc.Env b) -> SpecCalc.Env b

 %% Temporary to get stuff working
 op foldL: fa(a,b) (a * b -> SpecCalc.Env b) -> b -> List a -> SpecCalc.Env b
 def foldL f e l =
   case l of
     | [] -> return e
     | x :: r -> {result <- f(x,e);
		  foldL f result r}
     

 def foldOverQualifierMap f e m =
   foldL (fn (x as (q,id),r) -> f(q, id, STHMap.eval(m,x), r))
     e (STHMap.domainToList m)

 def wildFindUnQualified (qualifier_map, id) =
   foldriAQualifierMap (fn (_, ii, val, results) ->
			if id = ii then
			  Cons (val, results)
			else
			  results)
                       []
		       qualifier_map
endspec
