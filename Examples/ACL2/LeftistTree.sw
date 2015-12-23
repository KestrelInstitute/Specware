(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

import /Examples/ACL2/IList

%%%%%%%%%%%%%%%
% LeftistTree %
%%%%%%%%%%%%%%%

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
    isLeftist left && isLeftist right 
    && rank = rrank + 1 && rrank <= lrank 
    && x <= lx && x <= rx
  | IBranch (rank, x, left as IBranch (lrank, lx, _, _), IEmpty) ->
    isLeftist left &&
    rank = 1 &&
    x <= lx
  | IBranch (rank, _, IEmpty, IEmpty) -> rank = 1
  | _ -> false

type LeftistTree = ITree | isLeftist

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

%%%%%%%%%%%%%%%%%%%
% Tree operations %
%%%%%%%%%%%%%%%%%%%

op makeLT (x:Int, tree1:LeftistTree, tree2:LeftistTree) : ITree =
if getRank tree2 <= getRank tree1
  then IBranch (1+getRank tree2, x, tree1, tree2)
else IBranch (1+getRank tree1, x, tree2, tree1)

op mergeLT (tree1:LeftistTree, tree2:LeftistTree) : LeftistTree =
case (tree1, tree2) of
  | (IEmpty, _) -> tree2
  | (_, IEmpty) -> tree1
  | (IBranch (_,x,l,r), IBranch (_,y,_,_)) | x <= y -> makeLT (x,l,mergeLT(r,tree2))
  | (_,                 IBranch (_,y,l,r))          -> makeLT (y,l,mergeLT(tree1,r))

proof ACL2 mergeLT
  (declare (xargs :measure (+ (itree-measure tree1) (itree-measure tree2))
                  :type-lemmas
                  ((defthm mergeLT-type-lemma1
                       (implies (and (itree-p x)
                                     (ibranch-p x))
                                (integerp (+ 1 (ibranch-arg1 x))))))
                  :type-args
                  (:hints (("Subgoal *1/4.54.2" 
                            :by (:instance mergeLT-type-lemma1 
                                           (x (IBRANCH-ARG1 (MERGELT TREE1 (IBRANCH-ARG4 TREE2))))))))))
end-proof

op findMinLT (tree:NonEmptyLeftistTree) : Int =
case tree of
  | IBranch (_,x,_,_) -> x

op insertLT (x:Int, tree:LeftistTree) : LeftistTree = mergeLT (IBranch (1, x, IEmpty, IEmpty), tree)

op deleteMinLT(tree:NonEmptyLeftistTree) : LeftistTree =
case tree of
  | IBranch (_,_,left,right) -> mergeLT (left, right)

proof ACL2 deleteMinLT
  (declare (xargs :type-lemmas
                  ((DEFTHM DELETEMIN-TYPE-LEMMA1
                       (IMPLIES (AND (ITREE-P TREE)
                                     (IBRANCH-P (IBRANCH-ARG3 TREE))
                                     (IBRANCH-P (IBRANCH-ARG4 TREE))
                                     (ISLEFTIST (IBRANCH-ARG3 TREE))
                                     (ISLEFTIST (IBRANCH-ARG4 TREE))
                                     (EQUAL (IBRANCH-ARG1 TREE)
                                            (+ 1
                                               (IBRANCH-ARG1 (IBRANCH-ARG4 TREE))))
                                     (<= (IBRANCH-ARG1 (IBRANCH-ARG4 TREE))
                                         (IBRANCH-ARG1 (IBRANCH-ARG3 TREE)))
                                     (NOT (IEMPTY-P TREE)))
                                (ITREE-P (MERGELT 
                                          (IBRANCH-ARG3 TREE)
                                          (IBRANCH-ARG4 TREE))))
                     :hints (("Goal" :in-theory (disable
                                                 mergeLT-type-constraint)
                                     :use 
                                     ((:instance mergeLT-type-constraint
                                                 (tree1 
                                                  (IBRANCH-ARG3 TREE))
                                                 (tree2
                                                  (IBRANCH-ARG4
  tree)))))))
                   (DEFTHM DELETEMIN-TYPE-LEMMA2
                       (IMPLIES (AND (ITREE-P TREE)
                                     (IBRANCH-P (IBRANCH-ARG3 TREE))
                                     (IBRANCH-P (IBRANCH-ARG4 TREE))
                                     (ISLEFTIST (IBRANCH-ARG3 TREE))
                                     (ISLEFTIST (IBRANCH-ARG4 TREE))
                                     (EQUAL (IBRANCH-ARG1 TREE)
                                            (+ 1
                                               (IBRANCH-ARG1 (IBRANCH-ARG4 TREE))))
                                     (<= (IBRANCH-ARG1 (IBRANCH-ARG4 TREE))
                                         (IBRANCH-ARG1 (IBRANCH-ARG3 TREE)))
                                     (NOT (IEMPTY-P TREE)))
                                (ISLEFTIST (MERGELT 
                                            (IBRANCH-ARG3 TREE)
                                            (IBRANCH-ARG4 TREE))))
                     :hints (("Goal" :in-theory 
                                     (disable mergeLT-type-constraint)
                                     :use ((:instance mergeLT-type-constraint
                                                      (tree1
                                                       (IBRANCH-ARG3 TREE))
                                                      (tree2
                                                       (IBRANCH-ARG4 TREE))))))))))
end-proof

% Tree operation proofs %

proof ACL2 rankIsLRT
  :hints (("Goal" :in-theory (enable lengthRightSpine getRank isLeftist LeftistTree-p)))
end-proof

%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Other tree functions %%
%%%%%%%%%%%%%%%%%%%%%%%%%%

op sizeITree (tree:ITree) : Nat =
case tree of
  | IEmpty -> 0
  | IBranch (_,_,left,right) -> 1 + (sizeITree left) + (sizeITree right)

theorem sizeITree_children is
fa (tree:NonEmptyLeftistTree)
  case tree of
    | IEmpty -> true
    | IBranch (_,_,_,_) -> true

%%%%%%%%%%%
% Sorting %
%%%%%%%%%%%

op IListToLeftistTree (l:IList) : LeftistTree =
case l of
  | INil -> IEmpty
  | ICons (x,rst) -> insertLT (x,IListToLeftistTree rst)

op LeftistTreeToIList (tree:LeftistTree) : IOrderedList =
case tree of
  | IEmpty -> INil
  | IBranch (_,x,_,_) -> ICons (x, LeftistTreeToIList (deleteMinLT tree))

proof ACL2 LeftistTreeToIList
  (declare (xargs :measure (sizeITree tree)))
end-proof

end-spec