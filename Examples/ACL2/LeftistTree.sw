spec

type ITree = 
  | IEmpty
  | IBranch Nat * Int * ITree * ITree

op lengthRightSpine (tree:ITree) : Nat =
case tree of
  | IEmpty -> 0
  | IBranch (_,_,_,right) -> 1 + lengthRightSpine right

op isLeftist (tree:ITree) : Bool =
case tree of
  | IEmpty -> true
  | IBranch (rank, x, left as IBranch (lrank, lx, _, _), right as IBranch (rrank, rx, _, _)) ->
    isLeftist left && isLeftist right && rank = rrank + 1 && rrank <= lrank 
  | IBranch (rank, x, left as IBranch (lrank, lx, _, _), IEmpty) ->
    isLeftist left &&
    rank = 1 
  | IBranch (rank, _, IEmpty, IEmpty) -> rank = 1
  | _ -> false

type LeftistTree = ITree | isLeftist
(*
op isNonEmpty (tree:LeftistTree) : Bool =
case tree of
  | IEmpty -> false
  | _ -> true

type NonEmptyLeftistTree = LeftistTree | isNonEmpty

op getRank (tree:LeftistTree) : Nat =
case tree of
  | IEmpty -> 0
  | IBranch (rank,_,_,_) -> rank

theorem rankIsLRT is
fa (tree:LeftistTree) lengthRightSpine tree = getRank tree

op makeLT (x:Int, tree1:LeftistTree, tree2:LeftistTree) : LeftistTree =
if getRank tree2 <= getRank tree1
  then IBranch (1+getRank tree2, x, tree1, tree2)
else IBranch (1+getRank tree1, x, tree2, tree1)

op mergeLT (tree1:LeftistTree, tree2:LeftistTree) : LeftistTree =
case (tree1, tree2) of
  | (IEmpty, _) -> tree2
  | (_, IEmpty) -> tree1
  | _ -> tree1

op findMinLT (tree:NonEmptyLeftistTree) : Int =
case tree of
  | IBranch (_,x,_,_) -> x

op insertLT (x:Int, tree:LeftistTree) : LeftistTree = mergeLT (IBranch (1, x, IEmpty, IEmpty), tree)

op deleteMinLT(tree:NonEmptyLeftistTree) : LeftistTree =
case tree of
  | IBranch (_,_,left,right) -> mergeLT (left, right)
*)
end-spec