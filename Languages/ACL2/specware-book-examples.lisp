(in-package "ACL2")

(include-book "~/Specware/Languages/ACL2/specware-book")

;;;;;;;;;;;;;;;;;;
;; BINARY TREES ;;
;;;;;;;;;;;;;;;;;;

(defcoproduct ITree
  (IEmpty)
  (IBranch integerp ITreep ITreep))

;; Doesn't type check because it doesn't assert
;; (integerp (+ 1 (ibranch-arg1 it)))
(defun-typed ITree-1+ :type ITreep (it :type ITreep)
  (case-of it
   ((IEmpty) it)
   ((IBranch x left right) 
    (IBranch (1+ x) (ITree-1+ left) (ITree-1+ right)))))

;;;;;;;;;;;
;; LISTS ;;
;;;;;;;;;;;

(defcoproduct IList
  (INil)
  (ICons integerp IListp))

(defun-typed ISingletonp :type booleanp (a :type IListp)
  (case-of a
   ((ICons _ (ICons _ _)) nil)
   ((ICons _ _) t)
   ((INil) nil)))

(defun-typed IAppend :type IListp (a :type IListp
                                   b :type IListp)
  (case-of a
   ((INil) b)
   ((ICons x xs) (ICons x (IAppend xs b)))))

(defthm-guarded IAppend-assoc
    (implies (and (IListp a)
                  (IListp b)
                  (IListp c))
             (equal (IAppend (IAppend a b) c)
                    (IAppend a (IAppend b c)))))

(defun-typed IRev :type IListp (a :type IListp)
  (case-of a
   ((INil) a)
   ((ICons head tail) (IAppend (IRev tail) (ICons head (INil))))))

(defthm IAppend-Nil
    (implies (and (IListp a)
                  (INilp b))
             (equal (IAppend a b) a)))

(defthm-guarded IRev-append
    (implies (and (IListp a)
                  (IListp b))
             (equal (IRev (IAppend a b))
                    (IAppend (IRev b)
                             (IRev a)))))

(defthm-guarded IRev-IRev
    (implies (IListp a)
             (equal (IRev (IRev a)) a)))

(defun-typed IMember :type booleanp (x :type integerp
                                     a :type IListp)
  (case-of a
   ((INil) nil)
   ((ICons y ys) (or (equal y x) (IMember x ys)))))

(defthm-guarded IMember-IAppend
    (implies (and (integerp x) (IListp a) (IListp b))
             (equal (IMember x (IAppend a b))
                    (or (IMember x a) (IMember x b)))))

(defthm not-equal-ICons
    (implies (and (IListp l)
                  (integerp x))
             (not (equal l (ICons x l))))
  :hints (("Goal" :in-theory (enable ICons))))

(defun-typed IList-to-list :type integer-listp (il :type IListp)
  (cond ((INilp il) nil)
        ((IConsp il)
         (let ((head (ICons-arg1 il))
               (tail (ICons-arg2 il)))
           (cons head (IList-to-list tail))))))

(defun-typed list-to-IList :type IListp (l :type integer-listp)
  (cond ((endp l) (INil))
        ((consp l)
         (ICons (car l) (list-to-IList (cdr l))))))

(defthm-typed ilist-list
    (implies (integer-listp l)
             (equal (list-to-IList 
