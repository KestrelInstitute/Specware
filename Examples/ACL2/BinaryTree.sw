(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

  type BinaryTree =
    | Empty
    | Node (Int * BinaryTree * BinaryTree)

  op addOneTree (tree:BinaryTree) : BinaryTree =
    case tree of
      | Empty -> Empty
      | Node (x,left,right) -> Node (x+1,addOneTree left,addOneTree right)
        
  proof ACL2 addOneTree
  (declare (xargs :measure (acl2-count tree)))
  end-proof


(*
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

  proof ACL2 -verbatim
(defthm root_flipTree
    (implies (and (binarytree-p tree)
                  (node-p tree))
             (equal (node-node-arg1 (fliptree tree))
                    (node-node-arg1 tree))))

(DEFTHM
 FLIPTREE_HEAPORDERED_LEMMA1
 (IMPLIES (AND (BINARYTREE-P TREE)
               (NODE-P TREE)
               (HEAPORDERED (FLIPTREE (NODE-NODE-ARG3 TREE)))
               (HEAPORDERED (FLIPTREE (NODE-NODE-ARG2 TREE)))
               (< (NODE-NODE-ARG1 (NODE-NODE-ARG2 TREE))
                  (NODE-NODE-ARG1 TREE))
               (< (NODE-NODE-ARG1 (NODE-NODE-ARG3 TREE))
                  (NODE-NODE-ARG1 TREE))
               (HEAPORDERED (NODE-NODE-ARG2 TREE))
               (HEAPORDERED (NODE-NODE-ARG3 TREE))
               (NODE-P (FLIPTREE (NODE-NODE-ARG2 TREE))))
          (< (NODE-NODE-ARG1 (FLIPTREE (NODE-NODE-ARG2 TREE)))
             (NODE-NODE-ARG1 TREE)))
 :INSTRUCTIONS
 (:PRO
   (:CLAIM (EQUAL (NODE-NODE-ARG1 (FLIPTREE (NODE-NODE-ARG2 TREE)))
                  (NODE-NODE-ARG1 (NODE-NODE-ARG2 TREE)))
           :HINTS (("Goal" :USE ((:INSTANCE ROOT_FLIPTREE
                                            (TREE (NODE-NODE-ARG2 TREE)))))))
   :BASH))
  end-proof

  theorem flipTree_heapOrdered is
  fa(tree:BinaryTree) (heapOrdered tree => heapOrdered (flipTree tree))
*)
(*
  theorem flipTree_addOneTree is
  fa(tree:BinaryTree) flipTree (addOneTree tree) = addOneTree (flipTree tree)

  proof ACL2 flipTree_addOneTree
  :otf-flg t
  end-proof
*)
end-spec