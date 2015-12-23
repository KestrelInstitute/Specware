(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

  import /Library/General/FiniteSequence
  %import ExtTypesAPI
  %import ExtExpressionImpl#MetaSlangExtExpr
  import GoalsA

  op find: [a] (a * a -> Bool) * a * FSeq a -> Option Nat
  def find(f, x, s) =
    if empty? s then None
    else if f (x, first(s)) then Some 0
      else let tlRes = find(f, x, rtail(s)) in
	case tlRes of
	  | Some n -> Some (1 + n)
	  | _ -> None
  
  
  type Tree

  op ind: Nat -> String
  def ind n =
    let
      def ind0(n) = if n=0 then "" else " "^(ind0(n-1))
    in
      %"["^Nat.toString(n)^"]"^
      ind0(n)

  op succind: Nat -> Nat
  def succind(n) = n+2

  op Tree.print: Tree -> String
  def Tree.print(t) =
    Tree.printAux(t, 0)

  op Tree.printAux: Tree * Nat -> String
  def Tree.printAux(t, n) =
    let sn = succind(n) in
    let sep = "\n"^(ind sn) in
    let sep = "(" in
    if empty? (children(t))
      then
	(node(t)).step
    else
      ((node(t)).step)^sep^(printAux(children(t), sn))^")"

  op Trees.printAux: FSeq Tree * Nat -> String
  def Trees.printAux(ts, n) =
    let sep = ", " in
    if empty? (rtail ts)
      then printAux(first(ts),n)
    else
      printAux(first(ts), n)^sep^printAux(rtail(ts), n)

  

      

  type Node
  op Node.print: Node -> String

  type Tree = Node * FSeq Tree

  type Node = {formula: Goal, proven: Bool, step: String, label: String}
  def Node.print(n) =
    n.label^": "^print(n.formula)

  op nodeEqual: Node * Node -> Bool
  def nodeEqual(n1, n2) = n1.label = n2.label

  op Tree.leaf?: Tree -> Bool
  def Tree.leaf?(t) =
    empty?(children(t))

  op initialNode: Node
  def initialNode = {formula = test, proven = false, step = "blue", label = "G1"}

  op mkNewNode: String * Goal -> Node
  def mkNewNode(l, g) =
    {formula = g, proven = false, step = "red", label = l}

  op mkNewNodes: String * FSeq Goal -> FSeq Node
  def mkNewNodes(l, gs) = mkNewNodesAux(l, gs, 0)

  op mkNewNodesAux: String * FSeq Goal * Nat -> FSeq Node
  def mkNewNodesAux(l, gs, n) =
    if empty? gs
      then empty
    else
      let label = l^"."^(toString n) in
      let node = mkNewNode(label, first(gs)) in
      node |> mkNewNodesAux(l, (rtail gs), n+1)

  op Tree.find: (Tree -> Bool) * Tree -> Option Tree
  def Tree.find(pred, t) =
    if pred(t) then Some t 
    else
      let ch = children(t) in
      Tree.findChildren(pred, ch)

  op Tree.findChildren: (Tree -> Bool)* FSeq Tree -> Option Tree
  def Tree.findChildren(pred, ch) =
    if empty? ch then None
    else
      case find(pred, first(ch)) of
	| Some t -> Some t
	| None -> Tree.findChildren(pred, rtail(ch))

  op allProven?: Tree -> Bool
  def allProven?(t) =
    case find ((fn tt -> ~((node(tt)).proven)), t) of
      | Some _ -> false
      | None -> true
    
  op mkNodeTrue: Node -> Node
  def mkNodeTrue(n) =
    {formula = n.formula, proven = true, step = n.step, label = n.label}

  op mkNodeStep: Node * String -> Node
  def mkNodeStep(n, s) =
    {formula = n.formula, proven = n.proven, step = s, label = n.label}

  op initialTree: Tree
  def initialTree = (initialNode, empty)

  type TreeX = Node * Tree
  op TreeX.print: TreeX -> String

  op initialTreeX: TreeX
  def initialTreeX = (initialNode, initialTree)

  def TreeX.print(t) =
    Node.print(focus(t))

  op focus: TreeX -> Node
  def focus(t) =
    let (n, _) = t in n

  op tree: TreeX -> Tree
  def tree(tx) =
    let (_, t) = tx in
    t

  op mkTreeX: Node * Tree -> TreeX
  def mkTreeX(f, t) = (f, t)

  op empty: TreeX

  op mvUp: TreeX -> TreeX
  op mvDown: TreeX -> TreeX
  op mvAcross: TreeX -> TreeX

  op mkTreeXNodeTrue: TreeX -> TreeX
  def mkTreeXNodeTrue(tx) =
    let n = focus(tx) in
    let t = tree(tx) in
    let nn = mkNodeTrue(n) in
    let newT = replaceNode(n, nn, t) in
    (nn, newT)

  op mkTreeXNodeStep: TreeX * String -> TreeX
  def mkTreeXNodeStep(tx, s) =
    let n = focus(tx) in
    let t = tree(tx) in
    let nn = mkNodeStep(n,s) in
    let newT = replaceNode(n, nn, t) in
    (nn, newT)

  op nextLeaf: TreeX -> TreeX
  def nextLeaf(tx) =
    let f = focus(tx) in
    let t = tree(tx) in
    let pT = parent(tx) in
    let pn = node(pT) in
    let ch = children(pT) in
    let Some i = find(nodeEqual, f, map node ch) in
    if i = length(ch) - 1
      then
	nextLeaf(mkTreeX(pn, pT))
    else
      mkTreeX(node(ch @ (i + 1)), t)

  op unProvenLeaf: TreeX -> TreeX
  def unProvenLeaf(tx) =
    let f = focus(tx) in
    let t = tree(tx) in
    let Some res = find ((fn tt -> ~((node(tt)).proven) && leaf? tt), t) in
    mkTreeX(node(res), t)


  op node: Tree -> Node
  def node(t) =
    let (n, _) = t in
    n

  op children: Tree -> FSeq Tree
  def children(t) =
    let (_, ch) = t in
    ch

  op mkTree: Node * FSeq Tree -> Tree
  def mkTree(n, ch) = (n, ch)

  op Tree.parentOpt: Tree * Node * Tree -> Option Tree
  def Tree.parentOpt(posRes, n, t) =
    if nodeEqual(n, node(t)) then Some posRes
    else
      Tree.parentOptList(t, n, children(t))

  op Tree.parentOptList: Tree * Node * FSeq Tree -> Option Tree
  def Tree.parentOptList(posRes, n, children) =
    let found = exists? (fn c -> nodeEqual(n, node(c))) children in
    if found
      then Some posRes
    else
      if empty?(children)
	then None
      else
	let firstChild = first(children) in
	let restChildren = rtail(children) in
	let lRes = Tree.parentOpt(posRes, n, firstChild) in
	case lRes of
	  | Some _ -> lRes
	  | None -> Tree.parentOptList(posRes, n, restChildren)
  
  op root?: TreeX -> Bool
  def root?(tx) =
    nodeEqual(focus(tx), node(tree(tx)))
  
  op Tree.parent: TreeX -> Tree
  def Tree.parent(tx) =
    let f = focus(tx) in
    let t = tree(tx) in
    if root?(tx) then tree(tx)
      else
	let Some tr = parentOpt(t, f, t) in
	tr

  op TreeX.parent: TreeX -> TreeX
  def TreeX.parent(tx) =
    let f = focus(tx) in
    let t = tree(tx) in
    if root?(tx) then tx
      else
	let Some tr = parentOpt(t, f, t) in
	mkTreeX(node(tr), t)

  op replaceNode: Node * Node * Tree -> Tree
  def replaceNode(on, nn, t) =
    let n = node(t) in
    if nodeEqual(n, on)
      then mkTree(nn, children(t))
    else
      mkTree(n, map (fn c -> replaceNode(on, nn, c)) (children(t)))

  op TreeX.propagateProven: TreeX -> TreeX
  def TreeX.propagateProven(tx) =
    let f = focus(tx) in
    let t = tree(tx) in
    let newT = propagateProven(t) in
    mkTreeX(f, newT)

  op Tree.propagateProven: Tree -> Tree
  def Tree.propagateProven(t) =
    let ch = children(t) in
    if empty?(ch)
      then t
    else
      let newCh = map propagateProven ch in
      let childrenProven = forall? (fn tt -> (node(tt)).proven) newCh in
      if childrenProven
	then mkTree(mkNodeTrue(node(t)), newCh)
      else
	mkTree(node(t), newCh)
  
  op addChildren: TreeX * FSeq Tree -> TreeX
  def addChildren(tx, ch) =
    if empty?(ch)
      then
	mkTreeXNodeTrue(tx)
    else
    let f = focus(tx) in
    let t = tree(tx) in
    let n = node(t) in
    let oldChildren = children(t) in
    if nodeEqual(f, n)
      then
	let newT = mkTree(n, ch) in
	if empty?(ch)
	  then
	    mkTreeX(f, newT)
	else
	  mkTreeX(f, newT)
	  %mkTreeX(node(first(ch)), newT)
    else
      if empty?(oldChildren)
	then tx
      else
	let newChildren = map (fn c -> tree(addChildren(mkTreeX(f, c), ch))) oldChildren in
	if empty?(ch)
	  then
	    mkTreeX(f, mkTree(n, newChildren))
	else
	  mkTreeX(f, mkTree(n, newChildren))
	  %mkTreeX(node(first(ch)), mkTree(n, newChildren))


  op root: Tree -> Node

  op leaf?: TreeX -> Bool

endspec
