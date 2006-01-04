spec

  import Trees

  type State = {tree: TreeX}
%  type State = {}

  op State.print: State -> String
  def State.print(s) = print s.tree

  op initialState: State
  def initialState = {tree = initialTreeX}

  op addSubGoals: State * FSeq Goal -> State
  def addSubGoals(s, gs) =
    let tree = s.tree in
    let newNodes = map (fn g -> {formula = g, proven = false, step = ""}) gs in
    let newTrees = map (fn n -> (n, [])) newNodes in
    s
    
%  def initialState = {}

endspec
