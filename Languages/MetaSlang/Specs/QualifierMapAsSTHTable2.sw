AnnSpec qualifying
%%% Curry on second element string so that wildFindUnQualified is fast
%%% Top map is hash table.  Second level is alist.

spec
 import QualifierMap
 import /Library/Structures/Data/Maps/SimpleAsSTHarray
 import /Library/Structures/Data/Maps/SimpleAsAlist

 sort AQualifierMap b  = STHMap.Map(String,Map.Map(String,b))   
 def foldriAQualifierMap f ini qm =
   foldi (fn(id,im,r) -> foldi(fn (q,v,r) -> f(q,id,v,r)) r im) ini qm
 def emptyAQualifierMap  = emptyMap       % 
 def findAQualifierMap    (qm, x, y)    =
   case STHMap.apply  (qm, y) of
     | Some im -> Map.apply(im,x)
     | None -> None
 def removeAQualifierMap  (qm, x, y)    =
   case STHMap.apply  (qm, y) of
     | Some im ->
       let new_im = Map.remove (im, x) in
       if new_im = Map.emptyMap
	 then STHMap.remove (qm, y)
       else if new_im = im then qm
	 else STHMap.update(qm,y,new_im)
     | None ->qm
 def insertAQualifierMap (qm, x, y, v) =
   case STHMap.apply  (qm, y) of
     | Some im -> STHMap.update(qm,y,Map.update (im, x, v))
     | None -> STHMap.update(qm,y,Map.update(Map.emptyMap,x,v))
 def mapAQualifierMap f m =
   STHMap.map (fn im -> map f im) m
 def mapiAQualifierMap f m =
   STHMap.mapi (fn (id,im) -> Map.mapi (fn (q,v) -> f(q,id,v)) im) m
 def mapiPartialAQualifierMap f m =
   STHMap.mapiPartial (fn (id,im) ->
		       let new_im = Map.mapiPartial (fn (q,v) -> f(q,id,v)) im in
		       if new_im = Map.emptyMap then None
			 else Some new_im)
     m
 def appAQualifierMap f m =
   STHMap.app (fn im -> Map.app f im) m
 def appiAQualifierMap  f m =
   STHMap.appi (fn (id,im) -> Map.appi (fn (q,v) -> f(q,id,v)) im) m
 def qualifiers m =
   STHMap.foldi (fn(_,im,quals) ->
		 Map.foldi (fn (qname,_,quals) ->
			    if member(qname,quals)
			      then quals
			      else cons(qname,quals))
		   quals im)
      [] m
 def qualifierIds m = STHMap.domainToList m

  op SpecCalc.return : fa (a) a -> SpecCalc.Env a
  op SpecCalc.monadBind : fa (a,b) (SpecCalc.Env a) * (a -> SpecCalc.Env b) -> SpecCalc.Env b

 %% Temporary to get stuff working
 op foldL: fa(a,b) (a * b -> SpecCalc.Env b) -> b -> List a -> SpecCalc.Env b
 def foldL f e l =
   case l of
     | [] -> return e
     | x :: r -> {result <- f(x,e);
		  foldL f result r}

 def foldOverQualifierMap f e qm =
   foldL (fn (id,r) ->
	  foldL (fn ((q,v),r) -> f(q, id, v, r))
	    r (STHMap.eval(qm,id)))
     e (STHMap.domainToList qm)

 def wildFindUnQualified (qm, id) =
   case STHMap.apply  (qm, id) of
     | Some im -> Map.imageToList im
     | None -> []
endspec
