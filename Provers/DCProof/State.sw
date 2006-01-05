spec

  import Trees

  type State = {treeX: TreeX}
%  type State = {}

  op State.print: State -> String
  def State.print(s) = print (focus(s.treeX))

  op initialState: State
  def initialState = {treeX = initialTreeX}

  op addSubgoals: State * FSeq Goal -> State
  def addSubgoals(s, gs) =
    let tx = s.treeX in
    if empty?(gs)
      then
	let newTreeX = mkTreeXNodeTrue(tx) in
	{treeX = newTreeX}
    else
      let label = (focus(tx)).label in
      let newNodes = mkNewNodes(label, gs) in
      let newTrees = map (fn n -> mkTree(n, empty)) newNodes in
      let newTreeX = addChildren(tx, newTrees) in
      {treeX = newTreeX}

  op nextGoal: State -> State
  def nextGoal(s) =
    let tx = s.treeX in
    let newTx = nextLeaf(tx) in
    {treeX = newTx}
    
%  def initialState = {}

endspec
