(* This does not currently use Allen-Cocke interval analysis to
discover structure in a control-flow graph.  Refs acm computing
surveys Sept 1986 Ryder & Paull Cifuentes UQ website, IEEE "New
Algorithms for Control-Flow Graph Structuring" Moretti, Chanteperdix,
Osorio 

Top-level function is nodeListToStructuredGraph
*)
Struct qualifying 
spec 
  import /Languages/MetaSlang/Specs/StandardSpec
  import /Library/Legacy/DataStructures/ListUtilities % For replaceNth findOptionIndex
  import /Languages/MetaSlang/Specs/Printer

  sort Index = Integer			% Acually Nat + -1

  sort Stat =
    | Assign MS.Term
    | Proc MS.Term
    | Return MS.Term

  sort NodeContent =
    %% First three for pure control flow graphs
    | Branch { condition   : MS.Term,
	       trueBranch  : Index,
	       falseBranch : Index }
    | Block { statements : List Stat,
	      next       : Index }
    | Return MS.Term
    %% Next three are for representing discovered structure in the graph
    | IfThen { condition  : MS.Term,
	       trueBranch : Index,
	       cont       : Index }
    | IfThenElse { condition   : MS.Term,
		   trueBranch  : Index,
		   falseBranch : Index,
		   cont        : Index }
    | Loop { condition : MS.Term,
	     preTest?  : Boolean,
	     body      : Index,
%	     endLoop   : Index,
	     cont      : Index }

  op noContinue: Index			% To represent return destination
  def noContinue = Integer.~ 1
    
  sort Node = Index * NodeContent * List Index % predecessors
  sort Graph = List Node		% In some topological order

  op nodeContent: Nat * Graph -> NodeContent
  def nodeContent(i,g) = (nth(g,i)).2

  op predecessors: Index * Graph -> List Index
  op successors: Index * Graph -> List Index

  def predecessors(i,g) =
    case nth(g,i) of
      | (_,_,preds) -> preds

  def successors(i,g) = if i = noContinue then []
                         else nodeSuccessors(nodeContent(i,g))

  op nodeSuccessors: NodeContent ->  List Index
  def nodeSuccessors nc =
    case nc of
      | Block {statements = _, next} -> [next]
      | Branch {condition = _, trueBranch, falseBranch} -> [trueBranch, falseBranch]
      | Return _ -> []
      | IfThen {condition, trueBranch, cont} -> [trueBranch,cont]
      | IfThenElse {condition, trueBranch, falseBranch, cont} ->
        [trueBranch, falseBranch]
      | Loop {condition, preTest?, body, cont} -> [body,cont]

  op setNodeContent: Index * NodeContent * Graph -> Graph
  def setNodeContent(i,newNodeContent,g) =
    case nth(g,i) of
      | (index,_,preds) ->
	replaceNth(i,g,(index,newNodeContent,preds))
	    
  op setDFSIndex: Index * Nat * Graph -> Graph
  def setDFSIndex(i,newDFSI,g) =
    case nth(g,i) of
      | (_,content,preds) ->
	replaceNth(i,g,(newDFSI,content,preds))

  op depthFirstIndex: Index * Graph -> Nat
  def depthFirstIndex(i,g) = (nth(g,i)).1

  op insertDFSIndices: Graph * Index -> Graph
  def insertDFSIndices (g,topIndex) =
    let
      def DFS(i,st as (count,seen,g)) =
	if member(i,seen) or i = noContinue  % ~1 test by LE
	  then st
	  else
	    let (count,seen,g) = DFSlist(successors(i,g),count,Cons(i,seen),g) in
	    (count + 1, seen, setDFSIndex(i,count,g))
      def DFSlist(ilst,count,seen,g) =
	foldl DFS (count,seen,g) ilst
    in
      (DFS(topIndex,(1,[],g))).3

  op descendantIndex?: Index * Index * Graph -> Boolean
  def descendantIndex?(i,j,g) = depthFirstIndex(i,g) < depthFirstIndex(j,g)

  op loopPredecessors: Index * Graph -> List Index
  def loopPredecessors(i,g) =
    filter (fn j -> descendantIndex?(j,i,g)) (predecessors(i,g))

  op commonSuccessor: Nat * Nat * Graph -> Nat
  def commonSuccessor(i,j,g) =
    let def breadthFirst(iS,jS,iSeen,jSeen,g) =
          case iS of
	    | x::riS ->
	      if member(x,jSeen) then x   % LE added ~1 test
		else
		let newIS = filter (fn x -> ~(member(x,iSeen) or member(x,riS)
					      or x = noContinue))
		              (successors(x,g))
		in
		%% Notice reversal of jS and riS
		breadthFirst(jS,riS ++ newIS,jSeen,Cons(x,iSeen),g)
	    | [] ->
	  case jS of
	    | x::rjS ->
	      if member(x,iSeen) then x   % LE added ~1 test
		else let newJS = filter (fn x -> ~(member(x,jSeen) or member(x,rjS)
					             or x = noContinue))
		                   (successors(x,g))
		     in
		     breadthFirst(rjS ++ newJS,iS,Cons(x,jSeen),iSeen,g)
	    | _ -> noContinue
    in
      breadthFirst([i],[j],[],[],g)

  op findTopIndex: Graph -> Index
  def findTopIndex(g) = 0
%     % Index of node with no predecessors
%     case findOptionIndex
%            (fn (nd,i) -> if nd.3 = [] then Some i else None)
% 	   g
%       of Some (topIndex,_) -> topIndex

  op exitNodes: List Index * Graph -> List Index
  def exitNodes(nds,g) =
    foldl (fn (nd,exits) ->
	   (filter (fn sn -> ~(member(sn,nds) or member(sn,exits)))
	      (successors(nd,g)))
	   ++ exits)
      [] nds

  op getAllPredecessorsBackTo: List Index * List Index * Graph -> List Index
  def getAllPredecessorsBackTo(nds,limitNds,g) =
    let def loop(nds,found,g) =
          case nds of
	    | [] -> found
	    | nd::rNds ->
	      if member(nd,found) %or member(nd,limitNds)
		then loop(rNds,found,g)
		else loop(rNds ++ (predecessors(nd,g)),Cons(nd,found),g)
    in
      loop(nds,limitNds,g)

  op nodeListToStructuredGraph: List NodeContent -> Graph
  def nodeListToStructuredGraph contentsList =
    graphToStructuredGraph(addPredecessors contentsList)
  
  op graphToStructuredGraph: Graph -> Graph
  def graphToStructuredGraph (baseG) =
    if baseG = [] then baseG else
    %% The new graph has the same number of nodes as the old one,
    %% with structured nodes replacing simple nodes.
    %% This makes it easier to use indices as references before the whole
    %% graph is computed.
    let topIndex = findTopIndex(baseG) in
    let baseG = insertDFSIndices (baseG,topIndex) in
    %% DFS indices tell which nodes are higher in the graph and are used to
    %% to determine which links are looping links
    let
      def buildStructuredGraph(nd:Index,exits,newG) =
	if member(nd,exits) or nd = noContinue then newG
	else
	case loopPredecessors(nd,baseG) of
	  | []  -> buildStraightLine(nd,exits,newG)
	  | preds ->
	    let loopExits = exitNodes(Cons(nd,getAllPredecessorsBackTo(preds,[nd],
								       baseG)),
				      baseG) in
	    buildLoop(nd,loopExits,exits,newG)
	  %% So far only one loop for node
	  %| x::rs -> buildLoops(n,x,rs,newG)

      def buildLoop(head,loopExits,exits,newG) =
        let (cond,body,cont,newG) = loopHead(head,loopExits,newG) in
	let newG = buildStructuredGraph(cont,exits,newG) in
	let newG = buildStructuredGraph(body,Cons(head,loopExits),newG) in
	let newG = setNodeContent(head,
				  Loop {condition = cond,
					preTest?  = true,
					body      = body,
					cont  = cont},
				  newG)
	in foldl (fn (x,newG) ->
		  if x = cont then newG
		    else buildStructuredGraph(x,exits,newG))
	     newG loopExits

      def loopHead(head,loopExits,newG) =
	case nodeContent(head,baseG) of
	  | Branch {condition, trueBranch, falseBranch} ->
	    if member(falseBranch,loopExits) % outside loop
	      then (condition, trueBranch, falseBranch,newG)
	      else % trueBranch should be outside loop
	    if member(trueBranch,loopExits)
	      then (negateTerm condition,falseBranch,trueBranch, newG)
	      else fail ("GraphAnalysis: only simple while loops recognized")
	  %% |   Currently only have loops that start with a loop test
	    
      def buildStraightLine(nd,exits,newG) =
        if nd = noContinue then newG else
	case nodeContent(nd,baseG) of
	  | Block {statements = _, next} ->
	    buildStructuredGraph (next,exits,newG)
	  | Branch {condition, trueBranch, falseBranch} ->
	    let cont = commonSuccessor(trueBranch,falseBranch,baseG) in
	    let newG = buildStructuredGraph(trueBranch, [cont],newG) in
	    let newG = buildStructuredGraph(falseBranch,[cont],newG) in
        % LE added last disjunct below. There may be no common succesor (cont = noContinue)
	    let newG = if cont = trueBranch or cont = falseBranch or cont = noContinue
	                then newG
			else buildStructuredGraph(cont,exits,newG) in
	    if falseBranch = cont
	      then setNodeContent(nd,IfThen {condition   = condition,
					     trueBranch  = trueBranch,
					     cont        = falseBranch},
				  newG)
	    else if trueBranch = cont
	      then setNodeContent(nd,IfThen {condition   = negateTerm condition,
					     trueBranch  = falseBranch,
					     cont        = trueBranch},
				  newG)
	      else setNodeContent(nd,IfThenElse {condition   = condition,
						 trueBranch  = trueBranch,
						 falseBranch = falseBranch,
						 cont        = cont},
				  newG)
	   | Return _ -> newG
    in
    case baseG of
      | [] -> []
      %% Assumes first node of baseG is the head of the graph
      | _::_ ->
        buildStructuredGraph (topIndex, [], baseG)

  op printGraph: Graph -> String
  op printNode : Node * Index -> String
  op printStat : Stat  -> String
  op printNodeContent : NodeContent -> String

  def printGraph(g) =
    let (str,_) = foldl (fn (nd,(str,i)) -> (str ^ "\n" ^ printNode (nd,i),i+1))
                    ("",0) g
    in str

  def printNode((DFSindex,content,preds),i) =
    "Node " ^ (Integer.toString i) ^ ": DFS index: " ^ (Integer.toString DFSindex)
      ^ " Preds: (" ^ (show " " (map Integer.toString preds))
      ^ ")\n  "
      ^ (printNodeContent content)

  def printNodeContent content =
    case content of
	  | Branch {condition, trueBranch, falseBranch} ->
	    "Branch Condn: " ^ (printTerm condition) ^ "\n  "
	    ^ "True branch: " ^ (Integer.toString trueBranch) ^ "\n  "
	    ^ "False branch: " ^ (Integer.toString falseBranch)
	  | Block {statements, next} ->
	    "Block: " ^ show "; " (map printStat statements)
	    ^ "\n  "
	    ^ "Next: " ^ (Integer.toString next)
	  | Return t ->
	    "Return: " ^ (printTerm t)
	  | IfThen {condition, trueBranch, cont} ->
	    "If: " ^ (printTerm condition) ^ "\n  "
	    ^ "True branch: " ^ (Integer.toString trueBranch) ^ "\n  "
	    ^ "Continue: " ^ (Integer.toString cont)
	  | IfThenElse {condition, trueBranch, falseBranch, cont} ->
	    "If: " ^ (printTerm condition) ^ "\n  "
	    ^ "True branch: " ^ (Integer.toString trueBranch) ^ "\n  "
	    ^ "False branch: " ^ (Integer.toString falseBranch) ^ "\n  "
	    ^ "Continue: " ^ (Integer.toString cont)
	  | Loop {condition, preTest?, body, cont} ->
	    (if preTest? then "While: " else "Until: ") ^ (printTerm condition) ^ "\n  "
	    ^ "Body:: " ^ (Integer.toString body) ^ "\n  "
	    ^ "Continue: " ^ (Integer.toString cont)

  def printStat st =
    case st of
      | Assign t -> "Assign " ^ (printTerm t)
      | Proc t -> "Proc " ^ (printTerm t)
      | Return t -> "Return " ^ (printTerm t)

  op addPredecessors: List NodeContent -> Graph
  def addPredecessors contentsList =
    mapi (fn (i,nc) -> (0,nc,findPredecessors(i,contentsList))) contentsList

  op findPredecessors: Index * List NodeContent -> List Index
  def findPredecessors(i,contentsList) =
    filter (fn j -> member(i,nodeSuccessors(nth(contentsList,j))))
      (enumerate(0,(length contentsList) - 1))
	    
end
