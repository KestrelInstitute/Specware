(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Merge Union -- Stateful}

The performance of this merge union should be O(inverse_ackerman * size Map), where:
\begin{itemize}
\item {inverse_ackerman} is essentially 3 for all practical purposes (i.e, maps up to size 7,625,597,484,987)
\item {size Map        } is the number of elements in Map 
\end{itemize}

See MuSet.sw for the preferred implementation that uses purely functional updates.

\begin{spec}
spec 
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
 import /Library/Legacy/Utilities/State

 type MergeUnionMap  (key, value) = Map (key, MergeUnionNode value)

 type MergeUnionNode value = {rank   : Ref Nat,
			      parent : Ref (Option (MergeUnionNode value)),
			      value  : value}

 op merge : fa (a) MergeUnionNode a * MergeUnionNode a -> ()

 op initMergeUnionMap : fa (a, b) Map(a, b) -> MergeUnionMap(a,b)

 def initMergeUnionMap given_map =
  foldMap (fn new_mu_set_map -> fn key -> fn value ->
	   let node = {rank   = Ref 0, 
		       parent = Ref None,
		       value  = value}
	   in
	     (node.parent := Some node;
	      update new_mu_set_map key node))
          emptyMap
          given_map
			 
 def merge (node_a, node_b) =
  let def find_root node =
       case ! node.parent of
        | Some parent ->
          if node = parent then
	    node
	  else
	    find_root parent
  in
  let root_a = find_root node_a in
  let root_b = find_root node_b in
  let rank_a = ! root_a.rank in
  let rank_b = ! root_b.rank in
  ((if rank_a > rank_b then
      root_b.parent := Some root_a
    else
      root_a.parent := Some root_b);
   (if rank_a = rank_b then
      root_b.rank := 1 + ! root_b.rank
    else
      ()))

end      
\end{spec}
