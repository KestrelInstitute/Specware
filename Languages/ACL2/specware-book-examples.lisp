(in-package "ACL2")

(include-book "~/Specware/Languages/ACL2/specware-book")

;;;;;;;;;;;;;;;;;;
;; BINARY TREES ;;
;;;;;;;;;;;;;;;;;;

(defcoproduct BinaryTree
  (Empty)
  (Branch integerp BinaryTree-p BinaryTree-p))

(defun-typed (BinaryTree-p flipTree) ((BinaryTree-p tree))
  (case-of tree
   ((Branch x left right)
    (Branch x (flipTree right) (flipTree left)))
   (_ tree)))

(defun-typed (BinaryTree-p 1+-tree) ((BinaryTree-p tree))
  (case-of tree
   ((Branch x left right)
    (Branch (1+ x) (1+-tree left) (1+-tree right)))
   (_ (Empty))))

(defthm-guarded flipTree-flipTree
  (implies (BinaryTree-p tree)
           (equal (flipTree (flipTree tree)) tree)))

(defpredicate heapOrdered ((BinaryTree-p tree))
  (case-of tree
   ((Branch x 
            (as left  (Branch lx _ _)) 
            (as right (Branch rx _ _)))
    (and (> x lx) (> x rx)
         (heapOrdered left)
         (heapOrdered right)))
   ((Branch x (as left (Branch lx _ _)) _)
    (and (> x lx) (heapOrdered left)))
   ((Branch x _ (as right (Branch rx _ _)))
    (and (> x rx) (heapOrdered right)))
   (_ t)))

(defpredicate evenTree ((BinaryTree-p tree))
  (case-of tree
   ((Branch x 
            (as left  (Branch _ _ _)) 
            (as right (Branch _ _ _)))
    (and (evenp x) (evenTree left) (evenTree right)))
   ((Branch x left right)
    (and (evenp x) (evenTree left) (evenTree right)))
   (_ t)))

(defthm-guarded flipTree-heapOrdered
    (implies (and (BinaryTree-p tree)
                  (heapOrdered tree))
             (heapOrdered (flipTree tree))))

;;;;;;;;;;;
;; LISTS ;;
;;;;;;;;;;;

(defcoproduct IList
  (INil)
  (ICons integerp IList-p))

(defun-typed (IList-p IAppend) ((IList-p a)
                                (IList-p b))
 (case-of a
  ((INil) b)
  ((ICons x xs) (ICons x (IAppend xs b)))))

(defthm-guarded IAppend-assoc
    (implies (and (IList-p a)
                  (IList-p b)
                  (IList-p c))
             (equal (IAppend (IAppend a b) c)
                    (IAppend a (IAppend b c)))))

(defun-typed (IList-p IRev) ((IList-p a))
  (pattern-match a
   ((INil) a)
   ((ICons head tail) (IAppend (IRev tail) (ICons head (INil))))))

(defthm IAppend-Nil
    (implies (and (IList-p a)
                  (INil-p b))
             (equal (IAppend a b) a)))

(defthm-guarded IRev-append
    (implies (and (IList-p a)
                  (IList-p b))
             (equal (IRev (IAppend a b))
                    (IAppend (IRev b)
                             (IRev a)))))

(defthm-guarded IRev-IRev
    (implies (IList-p a)
             (equal (IRev (IRev a)) a)))

(defun-typed (booleanp IMember) ((integerp x) 
                                 (IList-p a))
  (case-of a
   ((INil) nil)
   ((ICons y ys) (or (equal y x) (IMember x ys)))))

(defthm-guarded IMember-IAppend
    (implies (and (integerp x) (IList-p a) (IList-p b))
             (equal (IMember x (IAppend a b))
                    (or (IMember x a) (IMember x b)))))

;;;;;;;;;;;;;;;;;
;; EXPERIMENTS ;;
;;;;;;;;;;;;;;;;;

(defcoproduct Lang
  (LTrue)
  (LFalse)
  (LZero)
  (LSucc Lang-p)
  (LPred Lang-p)
  (LIsZero Lang-p)
  (LIf Lang-p Lang-p Lang-p))

(defpredicate Lang-or-nilp (x)
  (or (null x) (lang-p x)))

(defun-typed (booleanp is-numeric) ((Lang-p term))
  (case-of term
   ((LZero) t)
   ((LSucc t1) (is-numeric t1))
   (_ nil)))

(defun-typed (booleanp is-value) ((Lang-p term))
  (case-of term
   ((LTrue) t)
   ((LFalse) t)
   (t1 (is-numeric t1))))

;; GUARDS

(defun-typed (Lang-or-nilp eval1) ((Lang-p exp))
  (case-of exp
   ((LIf  (LTrue) t2  _) t2)
   ((LIf (LFalse)  _ t3) t3)
   ((LIf t1 t2 t3)
    (let ((t1_ (eval1 t1)))
      (if t1_
          (LIf t1_ t2 t3)
          nil)))
   ((LSucc t1)
    (let ((t1_ (eval1 t1)))
      (if t1_
          (LSucc t1_)
          nil)))
   ((LPred (LZero))
    (LZero))
   ((LPred (LSucc t1)) (is-numeric t1) t1)
   ((LPred t1)
    (let ((t1_ (eval1 t1)))
      (if t1_
          (LSucc t1_)
          nil)))
   ((LIsZero (LZero)) (LTrue))
   ((LIsZero (LSucc t1)) (is-numeric t1) (declare (ignore t1)) (LFalse))
   ((LIsZero t1)
    (let ((t1_ (eval1 t1)))
      (if t1_
          (LIsZero t1_)
          nil)))
   (_ nil)))

(defthm eval1-langp 
    (implies (and (lang-p exp) (eval1 exp)) 
             (lang-p (eval1 exp))))

(defun-typed (Lang-p eval-exp) ((Lang-p exp))
  (let ((exp_ (eval1 exp)))
    (if exp_
        (eval-exp exp_)
        exp)))
