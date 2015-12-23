(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Merge Union -- Functional}

The performance of this merge union should be O(inverse_ackerman * size Map * access Map), where:
\begin{itemize}
\item {inverse_ackerman} is essentially 3 for all practical purposes (i.e, maps up to size 7,625,597,484,987)
\item {size   Map      } is the number of elements in Map 
\item {access Map      } is the performance of eval/update for the map implementation of MergeUnionMap,
                            which is typically O(Log N) for functional versions (e.g. splay or red/black 
                            trees) and O(1) for destructive versions (e.g. hashtables).
\end{itemize}

Hence if MergeUnionMap is implemented as a map with constant access time (e.g. a hashtable),
the performance of this merge union algorithm should be O(N).

See StatefulMuSet.sw for a less preferred implementation that uses destructive updates 
to avoid the logarithmic time penalties associated with functional maps and the 
constant time penalties associated with cloning nodes for functional updates.

\begin{spec}
spec {
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists

 type MergeUnionMap  (key, value) = Map (key, MergeUnionNode (key, value))

 type MergeUnionNode (key, value) = {rank   : Nat,
				     parent : Option (MergeUnionNode (key, value)),
				     key    : key,
				     value  : value}

 op initMergeUnionMap    : fa (a, b) Map(a, b) -> MergeUnionMap(a,b)
 op merge                : fa (a,b) MergeUnionMap (a,b) * MergeUnionNode (a,b) * MergeUnionNode (a,b) -> MergeUnionMap (a,b)
 op extractQuotientLists : fa (a,b) MergeUnionMap (a,b) -> List (List (MergeUnionNode (a,b)))

 def initMergeUnionMap key_value_map =
  foldMap (fn new_mu_map -> fn key -> fn value ->
	   update new_mu_map key {rank   = 0, 
				  parent = None,
				  key    = key,
				  value  = value})
          emptyMap
          key_value_map
			 
 def merge (mu_map, mu_node_a, mu_node_b) =
  let def find_root (mu_map, mu_node) =
       case mu_node.parent of
        | Some parent -> let (mu_map, root) = find_root (mu_map, parent) in
                         (update mu_map mu_node.key {rank   = mu_node.rank,
						     parent = Some root,
						     key    = mu_node.key,
						     value  = mu_node.value},
			  root)
        | None        -> (mu_map, mu_node)
  in
  let (mu_map, root_a) = find_root (mu_map, mu_node_a) in
  let (mu_map, root_b) = find_root (mu_map, mu_node_b) in
  let rank_a = root_a.rank in
  let rank_b = root_b.rank in
  let root_key_a  = root_a.key in
  let root_key_b  = root_b.key in
  if rank_a > rank_b then
    update mu_map root_key_b {rank   = root_b.rank,
			      parent = Some root_a,
			      key    = root_key_b,
			      value  = root_b.value}
  else 
    if rank_a < rank_b then
      update mu_map root_key_a {rank   = root_a.rank,
				parent = Some root_b,
				key    = root_key_a,
				value  = root_a.value}
    else      
      update (update mu_map root_key_a {rank   = root_a.rank,
					parent = Some root_b,
					key    = root_key_a,
					value  = root_a.value})
             root_key_b
	     {rank   = root_b.rank + 1,
	      parent = None,
	      key    = root_key_b,
	      value  = root_b.value}

 def fa (a,b) extractQuotientLists (mu_map : MergeUnionMap (a,b)) =
  %% First, build a map from root keys to lists of nodes.
  let root_map = 
      foldMap (fn root_map -> fn _ (* key *) -> fn mu_node -> 
	        %% ignore mu_node's key, since we only care about root's key
                let root = findRoot (mu_map, mu_node) in 
		update root_map 
		       root.key 
		       (Cons (mu_node,
			      case evalPartial root_map root.key of
                               | None      -> Nil
			       | Some list -> list)))
             (emptyMap : Map (a, List (MergeUnionNode (a,b))))
   	     mu_map
  in
  %% Then extract a list of lists from that map.
  %% (The root keys are no longer of any interest.)
  foldMap (fn result -> fn _ (* root_key *) -> fn mu_node_list ->  
	   Cons (mu_node_list, result))
          []
          root_map

 def findRoot (mu_map, mu_node) =
  case mu_node.parent of
   | None        -> mu_node
   | Some parent -> 
     let parent_node = eval mu_map parent.key in
     if parent_node = mu_node then
       mu_node
     else
       findRoot (mu_map, parent_node)

} 

\end{spec}
    
