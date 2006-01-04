spec

  import /Library/General/FiniteSequences
  %import ExtTypesAPI
  import ExtExpressionImpl#MetaSlangExtExpr

  type Tree
  op Tree.print: Tree -> String

  type Node
  op Node.print: Node -> String

  type Tree = Node * List Tree

  type Node = {formula: Expression, proven: Boolean, step: String}
  def Node.print(n) =
    print(n.formula)

  op initialNode: Node
  def initialNode = {formula = test, proven = false, step = ""}

  op initialTree: Tree
  def initialTree = (initialNode, [])

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
  op empty: TreeX

  op mvUp: TreeX -> TreeX
  op mvDown: TreeX -> TreeX
  op mvAcross: TreeX -> TreeX


  op children: TreeX -> FSeq TreeX

  op addChildren: TreeX -> TreeX

  op root: Tree -> Node

  op leaf?: TreeX -> Boolean

  op mkTree: Tree * FSeq Tree -> Tree

endspec


  