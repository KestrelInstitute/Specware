spec

%%fixme add to library
proof ACL2 -verbatim
  (defthmd split-equal
    (implies (and (booleanp x)
                  (booleanp y))
             (equal (equal x y)
                    (and (implies x y)
                         (implies y x)))))

  (defthm cancel_ones
    (implies (and (natp x) (natp y))
    (equal (< (+ 1 x)
              (+ 1 y))
           (< x y)))
           :hints (("Goal" :in-theory (enable split-equal))))
end-proof

  %%%%%%%%%
  % IList %
  %%%%%%%%%



  type IList =
    | INil
    | ICons Int * IList

  %%%%%%%%%%%%%%%%%%%%%%%%%%
  % IAppend, IRev, ILength %
  %%%%%%%%%%%%%%%%%%%%%%%%%%

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

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % ISubBag, IPerm, IOrdered %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op IHowMany (x:Int, a:IList) : Nat = 
  case a of
    | INil -> 0
    | ICons (y,ys) | x = y -> 1 + IHowMany (x,ys)
    | ICons (_,ys)         -> IHowMany (x,ys)

  theorem IHowmany_of_inil is
  fa(x:Int) IHowMany(x, INil) = 0

  op ISubBag (a:IList, b:IList) : Bool =
  case a of
    | INil -> true
    | ICons (x,xs) -> IHowMany (x,a) <= IHowMany (x,b) && ISubBag (xs,b)

  theorem ISubBag_ICons is
  fa(x:Int, a:IList, b:IList) ISubBag (a,b) => ISubBag (a, ICons(x,b))

  theorem ISubBag_reflexive is
  fa (a:IList) ISubBag (a,a)

  theorem ISubBag_transitive is
  fa (a:IList, b:IList, c:IList) ISubBag(a,b) && ISubBag(b,c) => ISubBag(a,c)

  theorem ISubBag_IHowManyLE is
  fa (x:Int, a:IList, b:IList) ISubBag(a,b) => IHowMany(x,a) <= IHowMany(x,b)

  op IPerm (a:IList, b:IList) : Bool =
  ISubBag (a,b) && ISubBag (b,a)

  op IOrdered (a:IList) : Bool =
  case a of
    | INil -> true
    | ICons (_,INil) -> true
    | ICons (x,rst as ICons (y,_)) ->
      x <= y && IOrdered rst

  type IOrderedList = IList | IOrdered

  theorem ISubBag_of_Nil is
    fa (a:IList) ISubBag(a,INil) = (a = INil)

  theorem ISubBag_of_Nil2 is
    fa (a:IList) ISubBag(INil,a) = true

  %%%%%%%%%%%%%%%%%%
  % IInsertionSort %
  %%%%%%%%%%%%%%%%%%

  op IInsert (x:Int, a:IOrderedList) : IOrderedList =
  case a of
    | INil -> ICons (x, INil)
    | ICons (y,ys) | x <= y -> ICons (x,a)
    | ICons (y,ys)          -> ICons (y, IInsert (x,ys))

proof ACL2 -verbatim
 (defthm ilist-p_of_iinsert
 (implies (and (IorderedLIST-P B)
               (integerp x))
          (ILIST-P (IINSERT X B)))
          :hints (("Goal" :in-theory (enable iinsert))))
end-proof




% put the perm in the type?
  op IInsertionSort (a:IList) : IOrderedList =
  case a of
    | INil -> INil
    | ICons (x,xs) -> IInsert (x,IInsertionSort xs)

%% fixme unfortunate that I need this.  defun-typed should do this?
proof ACL2 -verbatim      
(defthm IORDERED-of-ICONS-ICONS-ARG2
  (implies (and (IORDERED A)
                (ICONS-P A))
           (IORDERED (ICONS-ICONS-ARG2 A)))
  :hints (("Goal" :in-theory (enable IORDERED))))
end-proof

%% Eric's lemmas:
  theorem IHowMany_of_ICons_diff is
  fa(x:Int,y:Int,a:IList) ~(x=y) => (IHowMany(x,ICons(y,a)) = IHowMany(x,a))

  theorem IHowMany_of_ICons_same is
  fa(x:Int,y:Int,a:IList) IHowMany(x,ICons(x,a)) = 1 + IHowMany(x,a)

  theorem IHowMany_of_ICons_both is
  fa(x:Int,y:Int,a:IList) IHowMany(x,ICons(y,a)) = (if x = y then (1 + IHowMany(x,a)) else IHowMany(x,a))

  theorem IHowMany_of_IInsert_diff is
  fa(x:Int,y:Int,a:IOrderedList) ~(x=y) => (IHowMany(x,IInsert(y,a)) = IHowMany(x,a))

  theorem IHowMany_of_IInsert_same is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,IInsert(x,a)) = 1 + IHowMany(x,a)

  theorem IHowMany_of_IInsert_both is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,IInsert(y,a)) = (if x = y then (1 + IHowMany(x,a)) else IHowMany(x,a))

  proof ACL2 -verbatim
    (defthmd howmany-rationalp 
      (implies (and (integerp x) (ilist-p a)) 
               (rationalp (ihowmany x a)))
      :hints (("Goal" :in-theory (enable ihowmany))))
  end-proof

  theorem IHowManyLE_Insert_1 is
  fa(x:Int,a:IOrderedList,b:IList) IHowMany(x,a) <= IHowMany(x,b) => IHowMany(x,IInsert(x,a)) <= IHowMany(x,ICons(x,b))

  theorem IHowManyLE_Insert_2 is
  fa(x:Int,a:IList,b:IOrderedList) IHowMany(x,a) <= IHowMany (x,b) => IHowMany(x,a) <= IHowMany(x,IInsert(x,b))

  theorem IHowManyLE_Insert_3 is
  fa(x:Int,y:Int,a:IOrderedList) IHowMany(x,a) <= IHowMany(x,IInsert(y,a))


%%fixme needed for some guard conjecture.  expensive?
  proof ACL2 -verbatim
  (defthm rationalp-when-natp
    (implies (natp x)
             (rationalp x)))
end-proof

  theorem IHowManyLE_Insert_4 is
  fa(x:Int,a:IList,b:IOrderedList) IHowMany(x,a) <= IHowMany(x,b) => IHowMany(x,ICons(x,a)) <= IHowMany(x,IInsert(x,b))

%% fixme why is this needed?
proof ACL2 -verbatim
(defthm IORDEREDLIST-P_of_ICONS-ICONS-ARG2
        (implies (and (IORDEREDLIST-P A)
                      (NOT (INIL-P A)))
                 (IORDEREDLIST-P (ICONS-ICONS-ARG2 A)))
                 :hints (("Goal" :in-theory (enable IORDEREDLIST-P IORDERED))))
end-proof

  theorem ISubBag_IInsert_1 is
  fa(x:Int,a:IOrderedList,b:IList) ISubBag(a,b) => ISubBag(IInsert(x,a), ICons(x,b))
  

  theorem ISubBag_of_insert is
    fa (a:IOrderedList, x:Int) ISubBag(a,IInsert(x,a)) = true

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
                                    (IINSERTIONSORT (ICONS-ICONS-ARG2 A)))))))
  end-proof

  theorem IInsertionSortPerm is
  fa (a:IList) IPerm(a, IInsertionSort a)


  % Proofs %

  proof ACL2 IAppend_associative
    :hints (("Goal" :in-theory (enable IAppend)))
  end-proof

  proof ACL2 IAppend_INil
    :hints (("Goal" :in-theory (enable IAppend)))
  end-proof

  proof ACL2 IRev_IAppend
    :hints (("Goal" :in-theory (enable IAppend IRev)))
  end-proof

  proof ACL2 IRev_IRev
    :hints (("Goal" :in-theory (enable IAppend IRev)))
  end-proof

  proof ACL2 ILength_IAppend
    :hints (("Goal" :in-theory (enable IAppend ILength)))
  end-proof

  proof ACL2 IHowmany_of_inil
  :hints (("Goal" :in-theory (enable ihowmany)))
  end-proof

  proof ACL2 ISubBag_ICons
    :hints (("Goal" :in-theory (enable ISubBag IHowMany)))
  end-proof

  proof ACL2 ISubBag_reflexive
    :hints (("Goal" :in-theory (enable ISubBag)))
  end-proof

  proof ACL2 ISubBag_transitive
    :hints (("Goal" :in-theory (enable ISubBag IHowMany)))
  end-proof

  proof ACL2 ISubBag_IHowManyLE
    :hints (("Goal" :in-theory (enable ISubBag IHowMany)))
  end-proof

  proof ACL2 ISubBag_of_Nil
    :hints (("Goal" :in-theory (enable ISubBag ihowmany)))
  end-proof

  proof ACL2 ISubBag_of_Nil2
    :hints (("Goal" :in-theory (enable ISubBag ihowmany)))
  end-proof

%%fixme the need to enable IORDEREDLIST-P here is unfortunate
proof ACL2 IHowMany_of_IInsert_diff
    :hints (("Goal" :in-theory (enable IHowMany IInsert IORDEREDLIST-P)))
end-proof

proof ACL2 IHowMany_of_IInsert_same
    :hints (("Goal" :in-theory (enable IHowMany IInsert IORDEREDLIST-P)))
end-proof

proof ACL2 IHowMany_of_ICons_same
    :hints (("Goal" :in-theory (enable IHowMany)))
end-proof

proof ACL2 IHowMany_of_ICons_diff
    :hints (("Goal" :in-theory (enable IHowMany)))
end-proof

proof ACL2 ISubBag_IInsert_1
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (enable IINSERT ISubBag IHOWMANY)))
end-proof

  proof ACL2 ISubBag_of_insert
    :hints (("Goal" :in-theory (enable ISubBag IInsert ihowmany)))
  end-proof

  proof ACL2 IInsert
    (declare (xargs :type-constraint-args
                    (:hints (("Goal" :in-theory 
                                     (enable IOrderedList-p
                                             IOrdered))))
                    :verify-guards-args
                    (:hints (("Goal" :in-theory
                                     (enable IOrderedList-p
                                             IOrdered))))))
  end-proof

  proof ACL2 IInsertionSort
    (declare (xargs :type-constraint-args
                    (:hints (("Goal" :in-theory 
                                     (enable IOrderedList-p
                                             IOrdered))))
                    :verify-guards-args
                    (:hints (("Goal" :in-theory
                                     (enable IOrderedList-p
                                             IOrdered))))))
  end-proof

  proof ACL2 IHowManyLE_Insert_1
    :body-declare
    (declare (xargs :verify-guards-args
                    (:hints (("Goal" :in-theory (enable IOrderedList-p
                                                        IOrdered
                                                        IHowMany
                                                        howmany-rationalp))))))
    :hints (("Goal" :in-theory (enable IHowMany IInsert IOrderedList-p IOrdered)))
  end-proof
 
  proof ACL2 IHowManyLE_Insert_2
    :hints (("Goal" :in-theory (enable IHowMany IInsert IOrderedList-p IOrdered)))
  end-proof

proof ACL2 IInsertionSortPerm
      :hints (("Goal" :in-theory (enable IINSERTIONSORT iperm ISUBBAG)))
end-proof

end-spec
