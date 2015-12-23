(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Merge/Find Sets -- Functional}

For a description of the MFSet ADT (merge/find sets), see
Data Structures and Algorithms, by Aho, Hopcroft, and Ullman,
1983, pages 184-189.

The version implemented here is a (slightly? slower) functional variant.

Note: This version also uses value (of type Element) itself as the key
in MFSetMap, implemented as a PolyMap; as opposed to using keys such
as integers in a more efficient map.  It's quite plausible that using
Int for the key and Int * Element for the value would be faster.

This algorithm initializes the parent link for each node to None, and
its rank to 0, and then revises the parent links in such a manner that
all the nodes in the same equivalence class will have the same root
ancestor, except for that root node itself, whose parent will be None.

When merging elements from two classes, it makes the root of the
smaller class a child of the root of the larger class, and compresses
paths to roots in the process.

In fact, the performance of this merge union should be 
O(N * inverse_ackerman(N) * access(N)), where:

\begin{itemize}
\item {N                  } is the number of elements in Map 
\item {inverse_ackerman(N)} is essentially 3 for all practical purposes (i.e, maps up to size 7,625,597,484,987)
\item {access(N)          } is the performance of eval/update for the map implementation of MFSetMap,
                            which is typically O(Log N) for functional versions (e.g. splay or red/black 
                            trees) and O(1) for destructive versions (e.g. hashtables).
\end{itemize}

Hence if MFSetMap is implemented as a typical tree-structured
functional map (e.g splay tree, red/black tree, etc.) with access time
of O(log N), the practical performance of this quotienting algorithm
should be O(N log N).

If MFSetMap were implemented as a map with constant access time
(e.g. a vector or even a hashtable), the practical performance of this
quotienting algorithm should be O(N).  See StatefulMFSet.sw for a less
preferred implementation that uses such destructive updates to avoid
the logarithmic time penalties associated with functional maps and the
constant time penalties associated with cloning nodes for functional
updates.

\begin{spec}
MFSet qualifying
spec {
 import /Library/Structures/Data/QuotientSets/Monomorphic/AsListOfLists
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists


 %% A given key always represents the same value, and in fact could be the value,
 %% but we distinguish them since the key may be a more efficient index into a map

 type MFSetNode = {rank   : Nat,
		   parent : Option MFSetNode,
		   value  : Element}

 type MFSetMap  = Map (Element, MFSetNode)

 %% Ops for building initial collection to be partitioned:
 op emptyMFSetMap   : MFSetMap  
 op augmentMFSetMap : MFSetMap -> Element              -> MFSetMap  
 op updateMFSetMap  : MFSetMap -> Element -> MFSetNode -> MFSetMap  

 %% Ops optimized by this ADT:
 op merge : MFSetMap -> MFSetNode -> MFSetNode -> MFSetMap 
 op find  : MFSetMap -> Element   -> Element

 %% Op for extracting result:
 op extractQuotientSet : MFSetMap -> QuotientSet

 %%  ========================================================================

 def emptyMFSetMap = emptyMap

 def augmentMFSetMap mu_map element =
   %% functional version, presumably O(log N)  (imperative version could be O(1))
   update mu_map element {rank   = 0, 
			  parent = None,
			  value  = element}

 def updateMFSetMap mu_map element node = 
   %% functional version, presumably O(log N)  (imperative version could be O(1))
   update mu_map element node
			 
 %%  ========================================================================

 def merge mu_map mu_node_a mu_node_b =
  % let _ = toScreen ("\n===============\n") in
  % let _ = toScreen ("Merging\n") in
  % let _ = toScreen ((anyToString mu_node_a) ^ "\n") in
  % let _ = toScreen ((anyToString mu_node_b) ^ "\n") in
  let def find_root_node mu_map mu_node =
       %% "side effect" is to update map with new node whose parent is root,
       %% so we return new map as well as new node
       case mu_node.parent of
        | Some parent -> 
	  let (mu_map, root_node) = find_root_node mu_map parent in
	  let new_mu_node = {rank   = mu_node.rank,
			     parent = Some root_node,
			     value  = mu_node.value}
	  in
	    let new_map : MFSetMap = updateMFSetMap mu_map mu_node.value new_mu_node in
	    (new_map, root_node)

        | None        -> 
	  %% Careful -- we can't just use mu_node, since we might be looking at B1 in
	  %% at a situtation such as this, where B was promoted to rank 2 when A0 was
	  %% previously compared, but C0 still points at the old entry for B at rank 1,
          %% even though this old entry is no longer directly accessible via the mu_map.
	  %% A0 -------> B2
          %% C0 -> B1
	  %% D0 -------> E2
	  let new_mu_node = eval mu_map mu_node.value in
	  if new_mu_node = mu_node then
	    %% ok -- for this key (e.g. for "B" from B1), 
	    %%       the current map accesses the node we already had (B1),
	    %%       which is therefore a root node since it has no parent
	    (mu_map, mu_node)
	  else
	    %% oops -- for this key (e.g. for "B" from B1)
	    %%         the current map accesses a revised node (B2), 
	    %%         so continue from that revised node 
	    find_root_node mu_map new_mu_node
  in
  let (mu_map, root_a) = find_root_node mu_map mu_node_a in
  let (mu_map, root_b) = find_root_node mu_map mu_node_b in
  if root_a = root_b then
    mu_map
  else
    let rank_a = root_a.rank in
    let rank_b = root_b.rank in
    let root_value_b  = root_b.value in
    if rank_a > rank_b then
      updateMFSetMap mu_map 
                     root_value_b 
		     {rank   = root_b.rank,
		      parent = Some root_a,
		      value  = root_value_b}
    else 
      let root_value_a = root_a.value in
      if rank_a < rank_b then
	updateMFSetMap mu_map 
                       root_value_a
		       {rank   = root_a.rank,
			parent = Some root_b,
			value  = root_value_a}
      else      
	let new_root_node = {rank   = root_b.rank + 1,
			     parent = None,
			     value  = root_value_b}
	in
    	updateMFSetMap (updateMFSetMap mu_map
			               root_value_b 
				       new_root_node)		       
                       root_value_a
		       {rank   = root_a.rank,
			parent = Some new_root_node,
			value  = root_value_a}

 %%  ========================================================================

 def find mu_map value =
   findRootValue mu_map (eval mu_map value)

 def findRootValue mu_map mu_node =
  case mu_node.parent of
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

} 

\end{spec}
    
