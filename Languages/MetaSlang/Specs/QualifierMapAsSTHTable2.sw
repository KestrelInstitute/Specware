(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

AQualifierMapType =
AnnSpec qualifying
spec
 import /Library/Structures/Data/Maps/SimpleAsSTHarray
 import /Library/Structures/Data/Maps/SimpleAsAlist
 type AQualifierMap b  = STHMap.Map(String, MapL.Map(String,b))   
endspec

QualifierMapAsSTHTable2 =
%%% Curry on second element string so that wildFindUnQualified is fast
%%% Top map is hash table.  Second level is alist.

AnnSpec qualifying
spec
 import QualifierMap[morphism QualifierMap#AQualifierMapType -> AQualifierMapType {}]

 def foldriAQualifierMap f ini qm =
   foldi (fn(id,im,r) -> foldi(fn (q,v,r) -> f(q,id,v,r)) r im) ini qm
 def emptyAQualifierMap  = emptyMap       % 
 def findAQualifierMap    (qm, x, y)    =
   case STHMap.apply  (qm, y) of
     | Some im -> MapL.apply(im,x)
     | None -> None
 def removeAQualifierMap  (qm, x, y)    =
   case STHMap.apply  (qm, y) of
     | Some im ->
       let new_im = MapL.remove (im, x) in
       if new_im = MapL.emptyMap
	 then STHMap.remove (qm, y)
       else if new_im = im then qm
	 else STHMap.update(qm,y,new_im)
     | None ->qm
 def insertAQualifierMap (qm, x, y, v) =
   case STHMap.apply  (qm, y) of
     | Some im -> STHMap.update(qm,y, MapL.update (im, x, v))
     | None -> STHMap.update(qm,y, MapL.update(MapL.emptyMap,x,v))
 def mapAQualifierMap f m =
   STHMap.map (fn im -> map f im) m
 def mapiAQualifierMap f m =
   STHMap.mapi (fn (id,im) -> MapL.mapi (fn (q,v) -> f(q,id,v)) im) m
 def mapiPartialAQualifierMap f m =
   STHMap.mapiPartial (fn (id,im) ->
		       let new_im = MapL.mapiPartial (fn (q,v) -> f(q,id,v)) im in
		       if new_im = MapL.emptyMap then None
			 else Some new_im)
     m
 def [a] appAQualifierMap (f: a -> ()) (m: AQualifierMap a): () =
   STHMap.app (fn im -> MapL.app f im) m
 def [a] appiAQualifierMap (f: Qualifier * Id * a -> ()) (m: AQualifierMap a): () =
   STHMap.appi (fn (id,im) -> MapL.appi (fn (q,v) -> f(q,id,v)) im) m
 def [a] qualifiers (m: AQualifierMap a): List Qualifier =
   STHMap.foldi (fn(_,im,quals) ->
		 MapL.foldi (fn (qname,_,quals) ->
			    if qname in? quals
			      then quals
			      else Cons(qname,quals))
		   quals im)
      [] m
 def qualifierIds m = STHMap.domainToList m

 op SpecCalc.return : [a] a -> SpecCalc.Env a
 op SpecCalc.monadBind : [a,b] (SpecCalc.Env a) * (a -> SpecCalc.Env b) -> SpecCalc.Env b

 %% Temporary to get stuff working
 op foldL: [a,b] (a * b -> SpecCalc.Env b) -> b -> List a -> SpecCalc.Env b
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
     | Some im -> MapL.imageToList im
     | None -> []
endspec
