(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


(* Term discrimination nets

The following implementation is based on Tomas Uribe's 
support for term discrimination nets in STeP.
*)

TermDiscNet qualifying
spec
  import /Library/Legacy/DataStructures/IntSetSplay
  import /Library/Legacy/DataStructures/SplayMap

  type Disc_net = DNode

%% The labels that make up paths from root to nodes 

  type Key = Int
  def compareKey : Key * Key -> Comparison = 
      Integer.compare

  op findForPath   : (Disc_net * List Key ) -> 
			Option Disc_net
  op addForPath    : (Disc_net * List Key * Nat) -> Disc_net
  op removeForPath : (Disc_net * List Key * Nat) -> Disc_net

  op EmptyDiscNet : Disc_net

  type KeyMap a = SplayMap.Map(Key,a)
  def  empty = SplayMap.empty compareKey

  type DNode = IntSet.Set * KeyMap DNode

  def mkDnode cont = (cont,empty)

  def EmptyDiscNet = mkDnode IntSet.empty

  op contents(set: IntSet.Set, _:  KeyMap DNode): IntSet.Set = set
  op nextList(_: IntSet.Set, next: KeyMap DNode): KeyMap DNode = next

  op allContents(set: IntSet.Set, next: KeyMap DNode): IntSet.Set =
    foldl (fn (nd, result) -> IntSet.union(result,allContents nd)) set next

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
      if empty? rest 
	   then Some(node)
      else None



 (* This extend now returns the full extended net, not just the
  * last node: *)

   op extend : Disc_net * Key -> List Nat -> Disc_net % ?? guessing
  def extend ((set,next),element) = 
      fn [] ->  (IntSet.add(set,element),next)
       | (a::rest) -> 
         let newNode = extend ((mkDnode IntSet.empty),element) rest
	 in 
	 (set,SplayMap.insert(next,a,newNode))
	

  def addForPath = 
      fn ((set,next),[],element) -> (IntSet.add(set,element),next)
       | (dnode as (set,next), list as (k::rest), element) -> 
	 case getNext(next,k) 
           of None -> extend (dnode,element) list
	    | Some n ->
	      let newNode = addForPath(n, rest, element) in
	      (set,SplayMap.insert(next,k,newNode))
	
  def removeForPath = 
      fn ((set,next),[],element) -> (IntSet.delete(set,element),next)
       | ((set,next),(k::rest),element) -> 
	 case getNext(next,k)  
           of None -> 
	      System.fail (Nat.show element ^" Could not be removed")
	    | Some n ->
	      let newNode = removeForPath(n,rest,element) in
  	      (* Map.insert should replace the old entry with the new one *)
	      (set,SplayMap.insert(next,k,newNode))


(* The above two functions could be generalized to using just 
 * generic update functions, but it's not worth it. *)

  op  mergeDiscNets: Disc_net * Disc_net -> Disc_net
  def mergeDiscNets((s1,m1),(s2,m2)) =
    (IntSet.union(s1,s2),
     foldri (fn (key,val,m) ->
	      let newval =
		  case find(m,key) of
		    | None -> val
		    | Some oldval -> mergeDiscNets(val,oldval)
	      in
	      SplayMap.insert(m,key,newval))
       m1 m2)

endspec (* TermDiscNet *)
