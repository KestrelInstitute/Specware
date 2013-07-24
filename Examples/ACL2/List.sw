spec

  type IList =
    | INil
    | ICons Int * IList

  op IAppend (a:IList, b:IList) : IList = 
  case a of
    | INil -> b
    | ICons (x,xs) -> ICons (x, (IAppend (xs,b)))

  theorem IAppend_associative is
  fa (a:IList, b:IList, c:IList) (IAppend (IAppend (a,b), c) = IAppend (a, IAppend (b,c)))

  op IRev (a:IList) : IList =
  case a of
    | INil -> a
    | ICons (x,xs) -> IAppend (IRev xs, ICons (x,INil))

  theorem IAppend_INil is
  fa (a:IList) IAppend(a,INil) = a

  theorem IRev_IAppend is
  fa (a:IList,b:IList) IRev (IAppend (a,b)) = IAppend (IRev b, IRev a)

  theorem IRev_IRev is
  fa (a:IList) (IRev (IRev a)) = a

  op ILength (a:IList) : Int =
  case a of
    | INil -> 0
    | ICons (_,xs) -> 1 + ILength(xs)

  theorem ILength_IAppend is
  fa (a:IList,b:IList) ILength(IAppend(a,b)) = (ILength(a) + ILength(b))

  %%%%%%%%%%%
  % ISubBag %
  %%%%%%%%%%%

  op IHowMany (x:Int, a:IList) : Nat = 
  case a of
    | INil -> 0
    | ICons (y,ys) | x = y -> 1 + IHowMany (x,ys)
    | ICons (_,ys)         -> IHowMany (x,ys)

  op IHowManyLE (x:Int, a:IList, b:IList) : Bool =
  IHowMany (x,a) <= IHowMany (x,b)

  op ISubBag (a:IList, b:IList) : Bool =
  case a of
    | INil -> true
    | ICons (x,xs) -> IHowManyLE (x,a,b) && ISubBag (xs,b)

  theorem ISubBag_ICons is
  fa(x:Int, a:IList, b:IList) ISubBag (a,b) => ISubBag (a, ICons(x,b))

  theorem ISubBag_reflexive is
  fa (a:IList) ISubBag (a,a)

  theorem ISubBag_transitive is
  fa (a:IList, b:IList, c:IList) ISubBag(a,b) && ISubBag(b,c) => ISubBag(a,c)

  theorem ISubBag_IHowManyLE is
  fa (x:Int, a:IList, b:IList) ISubBag(a,b) => IHowManyLE(x,a,b)

  op IPerm (a:IList, b:IList) : Bool =
  ISubBag (a,b) && ISubBag (b,a)

  op IOrdered (a:IList) : Bool =
  case a of
    | INil -> true
    | ICons (_,INil) -> true
    | ICons (x,rst as ICons (y,_)) ->
      x <= y && IOrdered rst

  type IOrderedList = IList | IOrdered

  op IInsert (x:Int, a:IOrderedList) : IOrderedList =
  case a of
    | INil -> ICons (x, INil)
    | ICons (y,ys) | x <= y -> ICons (x,a)
    | ICons (y,ys)          -> ICons (y, IInsert (x,ys))

  op IInsertionSort (a:IList) : IOrderedList =
  case a of
    | INil -> INil
    | ICons (x,xs) -> IInsert (x,IInsertionSort xs)

  theorem IHowManyEQ_Insert is
  fa(x:Int,y:Int,a:IOrderedList) ~(x=y) => IHowMany(x,a) = IHowMany(x,IInsert(y,a))

  theorem IHowManyLE_Insert_1 is
  fa(x:Int,a:IOrderedList,b:IList) IHowManyLE(x,a,b) => IHowManyLE(x,IInsert(x,a),ICons(x,b))

  theorem IHowManyLE_Insert_2 is
  fa(x:Int,a:IList,b:IOrderedList) IHowManyLE(x,a,b) => IHowManyLE(x,a,IInsert(x,b))

  theorem IHowManyLE_Insert_3 is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,a) <= IHowMany(x,IInsert(y,a))

  theorem IHowManyLE_Insert_4 is
  fa(x:Int,a:IList,b:IOrderedList) IHowManyLE(x,a,b) => IHowManyLE(x,ICons(x,a),IInsert(x,b))

  proof ACL2 -verbatim
(DEFTHM
 ISUBBAG_IINSERT_1_LEMMA1
 (IMPLIES (AND (INTEGERP X)
               (ILIST-P A)
               (ICONS-P (ICONS-ICONS-ARG2 A))
               (<= (ICONS-ICONS-ARG1 A)
                   (ICONS-ICONS-ARG1 (ICONS-ICONS-ARG2 A)))
               (IORDERED (ICONS-ICONS-ARG2 A))
               (< (ICONS-ICONS-ARG1 A) X)
               (ICONS-P A)
               (ISUBBAG (IINSERT X (ICONS-ICONS-ARG2 A))
                        (ICONS X B))
               (ILIST-P B)
               (<= (+ 1
                      (IHOWMANY (ICONS-ICONS-ARG1 A)
                                (ICONS-ICONS-ARG2 A)))
                   (IHOWMANY (ICONS-ICONS-ARG1 A) B))
               (ISUBBAG (ICONS-ICONS-ARG2 A) B)
               (NOT (EQUAL (ICONS-ICONS-ARG1 A) X)))
          (<= (+ 1
                 (IHOWMANY (ICONS-ICONS-ARG1 A)
                           (IINSERT X (ICONS-ICONS-ARG2 A))))
              (IHOWMANY (ICONS-ICONS-ARG1 A) B)))
  :hints (("Goal" 
             :in-theory (disable IHOWMANYEQ_INSERT)
             :use ((:instance IHOWMANYEQ_INSERT
                      (X (ICONS-ICONS-ARG1 A))
                      (Y X)
                      (A (ICONS-ICONS-ARG2 A)))))))
  end-proof

  theorem ISubBag_IInsert_1 is
  fa(x:Int,a:IOrderedList,b:IList) ISubBag(a,b) => ISubBag(IInsert(x,a), ICons(x,b))
  
  proof ACL2 -verbatim
(DEFTHM
    ISUBBAG_IINSERT_2_LEMMA1
    (IMPLIES (AND (ILIST-P A)
                  (ILIST-P (IINSERT X B))
                  (ICONS-P A)
                  (ISUBBAG (ICONS-ICONS-ARG2 A) B)
                  (INTEGERP X)
                  (ILIST-P B)
                  (IORDERED B)
                  (<= (+ 1
                         (IHOWMANY (ICONS-ICONS-ARG1 A)
                                   (ICONS-ICONS-ARG2 A)))
                      (IHOWMANY (ICONS-ICONS-ARG1 A) B)))
             (<= (+ 1
                    (IHOWMANY (ICONS-ICONS-ARG1 A)
                              (ICONS-ICONS-ARG2 A)))
                 (IHOWMANY (ICONS-ICONS-ARG1 A)
                           (IINSERT X B))))
  :INSTRUCTIONS
  (:PRO (:CLAIM (<= (IHOWMANY (ICONS-ICONS-ARG1 A) B)
                    (IHOWMANY (ICONS-ICONS-ARG1 A)
                              (IINSERT X B)))
                :HINTS (("Goal" 
                           :IN-THEORY (DISABLE IHOWMANYLE_INSERT_3)
                           :USE ((:INSTANCE IHOWMANYLE_INSERT_3
                                    (X (ICONS-ICONS-ARG1 A))
                                    (A B)
                                    (Y X))))))
        :BASH))
  end-proof

  theorem ISubBag_IInsert_2 is
  fa(x:Int,a:IList,b:IOrderedList) ISubBag(a,b) => ISubBag(a,IInsert(x,b))

  proof ACL2 -verbatim
(defthm IInsertionSortPerm-lemma1
    (IMPLIES (AND (ILIST-P A)
                  (ICONS-P A)
                  (ILIST-P (IINSERTIONSORT (ICONS-ICONS-ARG2 A)))
                  (ISUBBAG (ICONS-ICONS-ARG2 A)
                           (IINSERTIONSORT (ICONS-ICONS-ARG2 A)))
                  (ISUBBAG (IINSERTIONSORT (ICONS-ICONS-ARG2 A))
                           (ICONS-ICONS-ARG2 A)))
             (<= (+ 1
                    (IHOWMANY (ICONS-ICONS-ARG1 A)
                              (ICONS-ICONS-ARG2 A)))
                 (IHOWMANY (ICONS-ICONS-ARG1 A)
                           (IINSERT (ICONS-ICONS-ARG1 A)
                                    (IINSERTIONSORT (ICONS-ICONS-ARG2 A))))))
  :hints (("Goal" 
             :in-theory (disable IHowManyLE_Insert_4)
             :use ((:instance IHowManyLE_Insert_4 
                      (x (icons-icons-arg1 a))
                      (a (icons-icons-arg2 a))
                      (b (iinsertionsort (icons-icons-arg2 a))))))))
  end-proof

  theorem IInsertionSortPerm is
  fa (a:IList) IPerm(a, IInsertionSort a)

end-spec
