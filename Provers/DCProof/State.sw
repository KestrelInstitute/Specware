(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

  import Trees

  type State = {treeX: TreeX}
%  type State = {}

  op State.print: State -> String
  def State.print(s) = print (focus(s.treeX))

  op State.printTree: State -> String
  def State.printTree(s) = print (tree(s.treeX))

  op initialState: State
  def initialState = {treeX = initialTreeX}

  op addSubgoals: State * FSeq Goal * String -> State
  def addSubgoals(s, gs, step) =
    let tx = s.treeX in
    if empty?(gs)
      then
	let newTreeX = mkTreeXNodeTrue(tx) in
	{treeX = newTreeX}
    else
      let label = (focus(tx)).label in
      let newNodes = mkNewNodes(label, gs) in
      let newTrees = map (fn n -> mkTree(n, empty)) newNodes in
      let newTreeX = mkTreeXNodeStep(tx, step) in
      let newTreeX = addChildren(newTreeX, newTrees) in
      {treeX = newTreeX}

  op setStep: State * String -> State
  def setStep(s, step) =
    let tx = s.treeX in
    let newTx = mkTreeXNodeStep(tx, step) in
    {treeX = newTx}

  op nextGoal: State -> State
  def nextGoal(s) =
    let tx = s.treeX in
    let newTx = unProvenLeaf(tx) in
    {treeX = newTx}

  op propagateProven: State -> State
  def propagateProven(s) =
    let tx = s.treeX in
    let newTx = propagateProven(tx) in
    {treeX = newTx}

  op proven: State -> Bool
  def proven(s) =
    let tx = s.treeX in
    allProven?(tree(tx))
    
%  def initialState = {}

endspec
