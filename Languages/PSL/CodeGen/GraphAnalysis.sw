(* This does not currently use Allen-Cocke interval analysis to
discover structure in a control-flow graph.  Refs acm computing
surveys Sept 1986 Ryder & Paull Cifuentes UQ website, IEEE "New
Algorithms for Control-Flow Graph Structuring" Moretti, Chanteperdix,
Osorio *)

spec 
  import /Languages/MetaSlang/Specs/StandardSpec
  import /Library/Legacy/DataStructures/ListUtilities

  sort Index = Nat

  sort Stat =
    | Assign Term * Term
    | Proc Term
    | Return Term

  sort NodeContent =
    %% First three for pure control flow graphs
    | Branch { condition   : Term,
	       trueBranch  : Index,
	       falseBranch : Index }
    | Block { statements : List Stat,
	      next       : Index }
    | Return Term
    %% Next three are for representing discovered structure in the graph
    | IfThen { condition  : Term,
	       trueBranch : Index,
	       continue   : Index }
    | IfThenElse { condition   : Term,
		   trueBranch  : Index,
		   falseBranch : Index,
		   continue    : Index }
    | Loop { condition : Term,
	     preTest?  : Boolean,
	     body      : Index,
	     endLoop   : Index,
	     continue  : Index }
    
  sort Node = Index * NodeContent * List Index % predecessors
  sort Graph = List Node		% In some topological order

  op nodeContent: Nat * Graph -> NodeContent
  def nodeContent(i,g) = (nth(g,i)).2

  op predecessors: Index * Graph -> List Index
  op successors: Index * Graph -> List Index

  def predecessors(i,g) =
    case nth(g,i) of
      | (_,_,preds) -> preds

  def successors(i,g) =
    case nodeContent(i,g) of
      | Block {statements = _, next} -> [next]
      | Branch {condition = _, trueBranch, falseBranch} -> [trueBranch, falseBranch]
      | Return _ -> []

  op depthFirstIndex: Index * Graph -> Nat
  def depthFirstIndex(i,g) = (nth(g,i)).1

  op descendantIndex?: Index * Index * Graph -> Boolean
  def descendantIndex?(i,j,g) = depthFirstIndex(i,g) < depthFirstIndex(j,g)

  op loopPredecessors: Index * Graph -> List Index
  def loopPredecessors(i,g) =
    filter (fn j -> descendantIndex?(j,i,g)) (successors(i,g))

  op commonSuccessor: Nat * Nat * Graph -> Nat
  def commonSuccessor(i,j,g) =
    let def breadthFirst(iS,jS,seen,g) =
          case iS of
	    | x::riS ->
	      if member(x,seen) then x
		else
		let newIS = filter (fn x -> ~(member(x,seen) or member(x,riS)))
		              (successors(x,g))
		in
		%% Notice reversal of jS and riS
		breadthFirst(jS,riS ++ newIS,Cons(x,seen),g)
	    | [] ->
	  case jS of
	    | x::riS ->
	      if member(x,seen) then x
		else breadthFirst(riS ++ successors(x,g),iS,Cons(x,seen),g)
	    | _ -> 0
    in
      breadthFirst([i],[j],[],g)

  op exitNodes: List Index * Graph -> List Index
  def exitNodes(nds,g) =
    foldl (fn (nd,exits) ->
	   (filter (fn sn -> ~(member(sn,nds) or member(sn,exits)))
	      (successors(nd,g)))
	   ++ exits)
      [] nds

  op getAllPredecessorsBackTo: Index * List Index * Graph -> List Index
  def getAllPredecessorsBackTo(nd,limitNds,g) =
    let def loop(nds,found,g) =
          case nds of
	    | [] -> found
	    | nd::rNds ->
	      if member(nd,nds) or member(nd,limitNds)
		then loop(rNds,found,g)
		else loop(rNds ++ (predecessors(nd,g)),Cons(nd,found),g)
    in
      loop([nd],limitNds,g)
  
  op graphToStructuredGraph: Graph -> Graph
  def graphToStructuredGraph (baseG) =
    %% The new graph has the same number of nodes as the old one,
    %% with structured nodes replacing simple nodes.
    %% This makes it easier to use indices as references before the whole
    %% graph is computed.
    let
      def replaceNode(i,newNodeContent,g) =
	%% Store node in graph
	case nth(g,i) of
	  | (index,_,preds) ->
	    replaceNth(index,g,(i,newNodeContent,preds))
	    
      def buildStructuredGraph(nd:Index,exits,newG) =
	case loopPredecessors(nd,baseG) of
	  | []  -> buildStraightLine(nd,exits,newG)
	  | [x] ->
	    let loopExits = exitNodes(Cons(nd,getAllPredecessorsBackTo(x,[nd],baseG)),
				      baseG) in
	    buildLoop(nd,x,loopExits,exits,newG)
	  %% So far only one loop for node
	  %| x::rs -> buildLoops(n,x,rs,newG)

      def buildLoop(head,endloop,loopExits,exits,newG) =
        let (cond,body,continue,newG) = loopHead(head,loopExits,newG) in
	let newG = buildStraightLine(continue,exits,newG) in
	let newG = buildStraightLine(body,Cons(head,loopExits),newG) in
	let newG = replaceNode(head,
			       Loop {condition = cond,
				     preTest?  = true,
				     body      = body,
				     endLoop   = endloop,
				     continue  = continue},
			       newG)
	in foldl (fn (x,newG) -> buildStraightLine(x,exits,newG))
	     newG loopExits

      def loopHead(head,loopExits,newG) =
	case nodeContent(head,baseG) of
	  | Branch {condition, trueBranch, falseBranch} ->
	    if member(falseBranch,loopExits) % outside loop
	      then (condition,           trueBranch, falseBranch,newG)
	      else % trueBranch should be outside loop
	    if member(trueBranch,loopExits)
	      then (negateTerm condition,falseBranch,trueBranch, newG)
	      else fail ("GraphAnalysis: only simple while loops recognized")
	  %% |   Currently only have loops that start with a loop test
	    
      def buildStraightLine(nd,exits,newG) =
	if member(nd,exits) then newG
	else
	case nodeContent(nd,baseG) of
	  | Block {statements = _, next} ->
	    buildStraightLine (next,exits,newG)
	  | Branch {condition, trueBranch, falseBranch} ->
	    let continue = commonSuccessor(trueBranch,falseBranch,baseG) in
	    let newG = buildStraightLine(trueBranch, [continue],newG) in
	    let newG = buildStraightLine(falseBranch,[continue],newG) in
	    let newG = buildStraightLine(continue,   exits,     newG) in
	    if falseBranch = continue
	      then replaceNode(nd,IfThen {condition   = condition,
					  trueBranch  = trueBranch,
					  continue    = falseBranch},
			      newG)
	    else if trueBranch = continue
	      then replaceNode(nd,IfThen {condition   = negateTerm condition,
					  trueBranch  = falseBranch,
					  continue    = trueBranch},
			      newG)
	      else replaceNode(nd,IfThenElse {condition   = condition,
					      trueBranch  = trueBranch,
					      falseBranch = falseBranch,
					      continue    = continue},
			       newG)
    in
    case baseG of
      | [] -> []
      %% Assumes first node of baseG is the head of the graph
      | _::_ -> buildStructuredGraph(1,[],baseG)

end