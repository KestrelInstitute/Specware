spec

  import /Library/Base/Empty

  type BList =
    | BNil
    | BCons Boolean * BList

  op BAppend (a:BList, b:BList) : BList = 
  case a of
    | BNil -> b
    | BCons (x,xs) -> BCons (x, (BAppend (xs,b)))

  theorem BAppend_associative is
  fa (a:BList, b:BList, c:BList) (BAppend (BAppend (a,b), c) = BAppend (a, BAppend (b,c)))

  op BRev (a:BList) : BList =
  case a of
    | BNil -> a
    | BCons (x,xs) -> BAppend (BRev xs, BCons (x,BNil))

  theorem BAppend_BNil is
  fa (a:BList) BAppend(a,BNil) = a

%  theorem BAppend_BNil is
%  fa (a:BList,b:BList) (b = BNil => BAppend (a,b) = a)

  theorem BRev_BAppend is
  fa (a:BList,b:BList) BRev (BAppend (a,b)) = BAppend (BRev b, BRev a)

  theorem BRev_BRev is
  fa (a:BList) (BRev (BRev a)) = a

end-spec

(*

(in-package "ACL2")
(include-book "~/Specware/Languages/ACL2/specware-book")

(defcoproduct BList
  (BNil)
  (BCons BCons-arg1 :type booleanp
         BCons-arg2 :type BListp))

(defun-typed BAppend :type BListp (a :type BListp
                                   b :type BListp)
   (cond ((BNilp a) b)
         ((BConsp a)
          (let ((x (BCons-arg1 a))
                (xs (BCons-arg2 a)))
           (BCons x (BAppend xs b))))))

(defthm-guarded BAppend-assoc
  (implies (and (BListp a)
                (BListp b)
                (BListp c))
           (equal (BAppend (BAppend a b) c)
                  (BAppend a (BAppend b c)))))

(defun-typed BReverse :type BListp (a :type BListp)
  (cond ((BNilp a) a)
        ((BConsp a)
         (let ((x  (BCons-arg1 a))
               (xs (BCons-arg2 a)))
          (BAppend (BReverse xs)
                   (BCons x (BNil)))))))

(defthm BReverse-BReverse
   (implies (BListp a)
            (equal (BReverse (BReverse a)) a)))

*)