... NOT IMPLEMENTED YET ...

\section{Merge/Find Sets -- Stateful}

For a description of the MFSet ADT (merge/find sets), see
Data Structures and Algorithms, by Aho, Hopcroft, and Ullman,
1983, pages 184-189.

The version implemented here is a (slightly slower) functional variant.

The performance of this merge union should be O(inverse_ackerman * size Map), where:
\begin{itemize}
\item {inverse_ackerman} is essentially 3 for all practical purposes (i.e, maps up to size 7,625,597,484,987)
\item {size Map        } is the number of elements in Map 
\end{itemize}

See MFSet.sw for the preferred implementation that uses purely functional updates.

\begin{spec}
StatefulMFSet qualifying
spec 
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
 import /Library/Legacy/Utilities/State

 %% Note: this assumes you can extract the appropriate key from a value in constant time.

 sort MFSetMap  (key, value) = Map (key, MFSetNode value)

 sort MFSetNode value = {rank   : Ref Nat,
			 parent : Ref (Option (MFSetNode value)),
			 value  : value}

 op merge : fa (a) MFSetNode a * MFSetNode a -> ()
 op find  : ...

 op extractQuotientSet : ...

 op initMFSetMap : fa (a, b) Map(a, b) -> MFSetMap(a,b)

 %%  ========================================================================

 def initMFSetMap given_map =
  foldMap (fn new_mu_set_map -> fn key -> fn value ->
	   let node = {rank   = Ref 0, 
		       parent = Ref None,
		       value  = value}
	   in
	     (node.parent := Some node;
	      update new_mu_set_map key node))
          emptyMap
          given_map
			 
 %%  ========================================================================

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

 %%  ========================================================================

end      
\end{spec}
