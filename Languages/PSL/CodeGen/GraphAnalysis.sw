(* This does not currently use Allen-Cocke interval analysis to
discover structure in a control-flow graph.  Refs acm computing
surveys Sept 1986 Ryder & Paull Cifuentes UQ website, IEEE "New
Algorithms for Control-Flow Graph Structuring" Moretti, Chanteperdix,
Osorio 

Top-level function is nodeListToStructuredGraph
*)

spec 
  import /Languages/MetaSlang/Specs/StandardSpec
  import /Library/Legacy/DataStructures/ListUtilities % For replaceNth findOptionIndex
  import /Languages/MetaSlang/Specs/Printer

  sort Index = Integer			% Acually Nat + -1

  sort Stat =
    | Assign Term
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

  op noContinue: Index			% To represent return destination
  def noContinue = ~ 1
    
  sort Node = Index * NodeContent * List Index % predecessors
  sort Graph = List Node		% In some topological order

  op nodeContent: Nat * Graph -> NodeContent
  def nodeContent(i,g) = (nth(g,i)).2

  op predecessors: Index * Graph -> List Index
  op successors: Index * Graph -> List Index

  def predecessors(i,g) =
    case nth(g,i) of
      | (_,_,preds) -> preds

  def successors(i,g) = nodeSuccessors(nodeContent(i,g))

  op nodeSuccessors: NodeContent ->  List Index
  def nodeSuccessors nc =
    case nc of
      | Block {statements = _, next} -> [next]
      | Branch {condition = _, trueBranch, falseBranch} -> [trueBranch, falseBranch]
      | Return _ -> []
      | IfThen {condition, trueBranch, continue} -> [trueBranch,continue]
      | IfThenElse {condition, trueBranch, falseBranch, continue} ->
        [trueBranch, falseBranch]
      | Loop {condition, preTest?, body, endLoop, continue} -> [body,continue]

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
	if member(i,seen)
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
	    | _ -> noContinue
    in
      breadthFirst([i],[j],[],g)

  op findTopIndex: Graph -> Index
  def findTopIndex(g) =
    % Index of node with no predecessors
    case findOptionIndex
           (fn (nd,i) -> if nd.3 = [] then Some i else None)
	   g
      of Some (topIndex,_) -> topIndex

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
	      if member(nd,found) %or member(nd,limitNds)
		then loop(rNds,found,g)
		else loop(rNds ++ (predecessors(nd,g)),Cons(nd,found),g)
    in
      loop([nd],limitNds,g)

  op nodeListToStructuredGraph: List NodeContent -> Graph
  def nodeListToStructuredGraph contentsList =
    graphToStructuredGraph(addPredecessors contentsList)
  
  op graphToStructuredGraph: Graph -> Graph
  def graphToStructuredGraph (baseG) =
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
	  | [x] ->
	    let loopExits = exitNodes(Cons(nd,getAllPredecessorsBackTo(x,[nd],baseG)),
				      baseG) in
	    buildLoop(nd,x,loopExits,exits,newG)
	  %% So far only one loop for node
	  %| x::rs -> buildLoops(n,x,rs,newG)

      def buildLoop(head,endloop,loopExits,exits,newG) =
        let (cond,body,continue,newG) = loopHead(head,loopExits,newG) in
	let newG = buildStructuredGraph(continue,exits,newG) in
	let newG = buildStructuredGraph(body,Cons(head,loopExits),newG) in
	let newG = setNodeContent(head,
				  Loop {condition = cond,
					preTest?  = true,
					body      = body,
					endLoop   = endloop,
					continue  = continue},
				  newG)
	in foldl (fn (x,newG) -> buildStructuredGraph(x,exits,newG))
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
	case nodeContent(nd,baseG) of
	  | Block {statements = _, next} ->
	    buildStructuredGraph (next,exits,newG)
	  | Branch {condition, trueBranch, falseBranch} ->
	    let continue = commonSuccessor(trueBranch,falseBranch,baseG) in
	    let newG = buildStraightLine(trueBranch, [continue],newG) in
	    let newG = buildStraightLine(falseBranch,[continue],newG) in
	    let newG = buildStraightLine(continue,   exits,     newG) in
	    if falseBranch = continue
	      then setNodeContent(nd,IfThen {condition   = condition,
					     trueBranch  = trueBranch,
					     continue    = falseBranch},
				  newG)
	    else if trueBranch = continue
	      then setNodeContent(nd,IfThen {condition   = negateTerm condition,
					     trueBranch  = falseBranch,
					     continue    = trueBranch},
				  newG)
	      else setNodeContent(nd,IfThenElse {condition   = condition,
						 trueBranch  = trueBranch,
						 falseBranch = falseBranch,
						 continue    = continue},
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

  def printGraph(g) =
    let (str,_) = foldl (fn (nd,(str,i)) -> (str ^ "\n" ^ printNode (nd,i),i+1))
                    ("",0) g
    in str

  def printNode((DFSindex,content,preds),i) =
    "Node " ^ (Integer.toString i) ^ ": DFS index: " ^ (Integer.toString DFSindex)
      ^ " Preds: (" ^ (foldl(fn (j,str) -> str ^ (Integer.toString j) ^ " ") "" preds)
      ^ ")\n  "
      ^ (case content of
	  | Branch {condition, trueBranch, falseBranch} ->
	    "Branch Condn: " ^ (printTerm condition) ^ "\n  "
	    ^ "True branch: " ^ (Integer.toString trueBranch) ^ "\n  "
	    ^ "False branch: " ^ (Integer.toString falseBranch)
	  | Block {statements, next} ->
	    "Block: " ^ (foldl (fn (st,str) -> str ^ (printStat st) ^ "; ") "" statements)
	    ^ "\n  "
	    ^ "Next: " ^ (Integer.toString next)
	  | Return t ->
	    "Return: " ^ (printTerm t)
	  | IfThen {condition, trueBranch, continue} ->
	    "If: " ^ (printTerm condition) ^ "\n  "
	    ^ "True branch: " ^ (Integer.toString trueBranch) ^ "\n  "
	    ^ "Continue: " ^ (Integer.toString continue)
	  | IfThenElse {condition, trueBranch, falseBranch, continue} ->
	    "If: " ^ (printTerm condition) ^ "\n  "
	    ^ "True branch: " ^ (Integer.toString trueBranch) ^ "\n  "
	    ^ "False branch: " ^ (Integer.toString falseBranch)
	    ^ "Continue: " ^ (Integer.toString continue)
	  | Loop {condition, preTest?, body, endLoop, continue} ->
	    (if preTest? then "While: " else "Until: ") ^ (printTerm condition) ^ "\n  "
	    ^ "Body:: " ^ (Integer.toString body) ^ "\n  "
	    ^ "End Loop: " ^ (Integer.toString endLoop) ^ "\n  "
	    ^ "Continue: " ^ (Integer.toString continue))

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