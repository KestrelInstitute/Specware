BinaryTree = spec

  type BinaryTree =
    | Empty
    | Node (Int * BinaryTree * BinaryTree)

  op flipTree (tree:BinaryTree) : BinaryTree =
    case tree of
      | Empty -> Empty
      | Node (x,left,right) -> Node (x,flipTree(right),flipTree(left))

  theorem flipTree_flipTree is
  fa(tree:BinaryTree) flipTree(flipTree tree) = tree

  op heapOrdered (tree:BinaryTree) : Bool =
    case tree of
      | Node (x, left as Node (lx,_,_), right as Node (rx,_,_)) ->
        x > lx && x > rx && heapOrdered left && heapOrdered right
      | Node (x, left as Node (lx,_,_), _) ->
        x > lx && heapOrdered left
      | Node (x, _, right as Node (rx,_,_)) ->
        x > rx && heapOrdered right
      | _ -> true

  theorem flipTree_heapOrdered is
  fa(tree:BinaryTree) (heapOrdered tree => heapOrdered (flipTree tree))

end-spec