
\section{Term discrimination nets}

The following implementation is based on Tomas Uribe's 
support for term discrimination nets in STeP.

\begin{spec}
TermDiscNet qualifying
spec
  import /Library/Legacy/DataStructures/IntSetSplay
  import SpecCalc qualifying /Library/Legacy/DataStructures/SplayMap

  sort disc_net = DNode

%% The labels that make up paths from root to nodes 

  sort Key = Integer
  def compareKey : Key * Key -> Comparison = 
      Integer.compare

  op findForPath   : (disc_net * List Key ) -> 
			Option IntegerSet.Set
  op addForPath    : (disc_net * List Key * Nat) -> disc_net
  op removeForPath : (disc_net * List Key * Nat) -> disc_net

  op EmptyDiscNet : disc_net

  sort KeyMap a = SplayMap.Map(Key,a)
  def  empty = SplayMap.empty compareKey

  sort DNode = IntegerSet.Set * KeyMap DNode

  def mkDnode cont = (cont,empty)

  def EmptyDiscNet = mkDnode IntegerSet.empty

  def contents(set,_) = set
  def nextList(_,nextLst) = nextLst

  op  getNext : KeyMap DNode * Key -> Option DNode
  def getNext = SplayMap.find

  op  nextNode : DNode * Key -> Option DNode

  def nextNode(dnode, key) = 
      SplayMap.find(nextList dnode, key)

(* "follow" returns the node at the end of the path together with
 * the portion of the path that was not used: *)

  op  follow : List Key * DNode -> DNode * List Key
  def follow = 
      fn ([],dnode) -> (dnode,[])
       | (list as (k::rest),dnode) -> 
	  case (nextNode(dnode,k)) 
            of None -> (dnode, list)
	     | Some next -> follow (rest,next)

  def findForPath(dNet, p) =
      let (node,rest) = follow (p,dNet) in
      if null rest 
	   then Some(contents node)
      else None



 (* This extend now returns the full extended net, not just the
  * last node: *)

   op extend : disc_net * Key -> List Nat -> disc_net % ?? guessing
  def extend ((set,next),element) = 
      fn [] ->  (IntegerSet.add(set,element),next)
       | (a::rest) -> 
         let newNode = extend ((mkDnode IntegerSet.empty),element) rest
	 in 
	 (set,SplayMap.insert(next,a,newNode))
	

  def addForPath = 
      fn ((set,next),[],element) -> (IntegerSet.add(set,element),next)
       | (dnode as (set,next), list as (k::rest), element) -> 
	 case getNext(next,k) 
           of None -> extend (dnode,element) list
	    | Some n ->
	      let newNode = addForPath(n, rest, element) in
	      (set,SplayMap.insert(next,k,newNode))
	
  def removeForPath = 
      fn ((set,next),[],element) -> (IntegerSet.delete(set,element),next)
       | ((set,next),(k::rest),element) -> 
	 case getNext(next,k)  
           of None -> 
	      System.fail (Nat.toString element ^" Could not be removed")
	    | Some n ->
	      let newNode = removeForPath(n,rest,element) in
  	      (* Map.insert should replace the old entry with the new one *)
	      (set,SplayMap.insert(next,k,newNode))


(* The above two functions could be generalized to using just 
 * generic update functions, but it's not worth it. *)

  op  mergeDiscNets: disc_net * disc_net -> disc_net
  def mergeDiscNets((s1,m1),(s2,m2)) =
    (IntegerSet.union(s1,s2),
     foldri (fn (key,val,m) ->
	      let newval =
		  case find(m,key) of
		    | None -> val
		    | Some oldval -> mergeDiscNets(val,oldval)
	      in
	      SplayMap.insert(m,key,newval))
       m1 m2)

endspec (* TermDiscNet *)
\end{spec}
