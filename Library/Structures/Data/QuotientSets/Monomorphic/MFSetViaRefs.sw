(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Merge/Find Sets -- Stateful}

For a description of the MFSet ADT (merge/find sets), see
Data Structures and Algorithms, by Aho, Hopcroft, and Ullman,
1983, pages 184-189.

The performance of this merge union should be O(inverse_ackerman * size Map), where:
\begin{itemize}
\item {inverse_ackerman} is essentially 3 for all practical purposes (i.e, maps up to size 7,625,597,484,987)
\item {size Map        } is the number of elements in Map 
\end{itemize}

See MFSet.sw for the preferred(?) implementation that uses purely functional updates.

\begin{spec}
MFSetViaRefs qualifying
spec 
 import /Library/Structures/Data/QuotientSets/Monomorphic/AsListOfLists
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
 import /Library/Legacy/Utilities/State

 %% Note: this assumes you can extract the appropriate key from a value in constant time.

 type MFSetMap   = Map (Element, MFSetNode)

 type MFSetNode  = {rank   : Ref Nat,
		    parent : Ref (Option MFSetNode),
		    value  : Element}

 %% Ops for building initial collection to be partitioned:
 op updateMFSetMap  : MFSetMap -> Element -> MFSetNode -> MFSetMap  



 %%  ========================================================================

 op  emptyMFSetMap : MFSetMap  
 def emptyMFSetMap = emptyMap

 op  augmentMFSetMap : MFSetMap -> Element -> MFSetMap  
 def augmentMFSetMap mu_map element =
   %% functional version, presumably O(log N)  (imperative version could be O(1))
   update mu_map element {rank   = Ref 0, 
			  parent = Ref None,
			  value  = element}

 op  initMFSetMap : Map(Element, Element) -> MFSetMap
 def initMFSetMap given_map =
  foldMap (fn new_mu_set_map -> fn key -> fn value ->
	   let node = {rank   = Ref 0, 
		       parent = Ref None,
		       value  = value}
	   in
	     update new_mu_set_map key node)
          emptyMap
          given_map
			 
 %%  ========================================================================

 op  merge : MFSetMap -> MFSetNode -> MFSetNode -> MFSetMap 
 def merge map node_a node_b =
  let def find_root node =
       case ! node.parent of
        | Some parent -> find_root parent
	| _ -> node
  in
  let root_a = find_root node_a in
  let root_b = find_root node_b in
  if root_a = root_b then
    map
  else
    let rank_a = ! root_a.rank in
    let rank_b = ! root_b.rank in
    let _ = if rank_a > rank_b then
              let _ = if root_a = root_b then writeLine "oops 1" else () in
	      root_b.parent := Some root_a
	    else 
	      let _ = if root_a = root_b then writeLine "oops 2" else () in
	      root_a.parent := Some root_b
    in
    let _ = if rank_a = rank_b then
              root_b.rank := 1 + ! root_b.rank
	    else
	      ()
    in
      map

 %%  ========================================================================

 op  find  : MFSetMap -> Element -> Element
 def find mu_map value =
   findRootValue mu_map (eval mu_map value)

 def findRootValue mu_map mu_node =
  case ! mu_node.parent of
   | None ->
     let new_mu_node = eval mu_map mu_node.value in
     if new_mu_node = mu_node then
       %% ok -- for this key (e.g. for "B" from B1), 
       %%       the current map accesses the node we already had (B1),
       %%       which is therefore a root node since it has no parent
       mu_node.value
     else
       %% oops -- for this key (e.g. for "B" from B1)
       %%         the current map accesses a revised node (B2), 
       %%         so continue from that revised node 
       findRootValue mu_map new_mu_node

   | Some old_parent_node -> 
     let current_parent_node = eval mu_map old_parent_node.value in
     findRootValue mu_map current_parent_node

 %%  ========================================================================

 %% Op for extracting result:
 op  extractQuotientSet : MFSetMap -> QuotientSet
 def extractQuotientSet mu_map =
  %% build a map from root elements to lists of equivalent elements
  let root_map = 
      foldMap (fn root_to_class_map -> fn element -> fn mu_node -> 
                let root_value = findRootValue mu_map mu_node in 
		let old_class_list = case evalPartial root_to_class_map root_value of
				       | None      -> Nil
				       | Some list -> list
		in
		update root_to_class_map 
                       root_value
		       (Cons (element, old_class_list)))
              (emptyMap : PolyMap.Map (Element, List Element))
   	      mu_map
  in
  %% Then extract a list of lists from that map.
  %% (The root keys are no longer of any interest.)
  foldMap (fn list_of_class_lists -> fn _ (* root_value *) -> fn class_list ->  
	   Cons (class_list, list_of_class_lists))
          []
          root_map

 %%  ========================================================================

end-spec
\end{spec}
