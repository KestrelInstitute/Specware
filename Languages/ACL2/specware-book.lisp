(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;
;; DEFTHM-GUARDED ;;
;;;;;;;;;;;;;;;;;;;;

(defmacro implies-macro (x y)
  (list 'if x (list 'if y 't 'nil) 't))

(mutual-recursion

 (defun implies-to-implies-macro (term)
   (if (atom term) 
       term
       (let ((fn-name (if (equal (car term) 'implies) 
                          'implies-macro 
                          (car term))))
         (cons fn-name (map-implies-to-implies-macro (cdr term))))))

 (defun map-implies-to-implies-macro (terms)
   (if (atom terms)
       nil
       (cons (implies-to-implies-macro (car terms))
             (map-implies-to-implies-macro (cdr terms))))))

(defmacro defthm-guarded (name term)
  (list 'progn
        (list 'defthm name (implies-to-implies-macro term)
              ':rule-classes 
              (list (list ':rewrite
                          ':corollary
                          term
                          ':hints
                          (list (list '"Goal" 
                                      ':in-theory 
                                      (list 'theory '(quote minimal-theory))))
                          )))
        (list 'verify-guards name)))

;;;;;;;;;;;;;;;;;;;
;; XOR-ALL MACRO ;;
;;;;;;;;;;;;;;;;;;;

(defun xor-all-macro (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (if (consp (cdr lst))
          (list 'if
                (car lst)
                (list 'not 
                      (if (consp (cddr lst))
                          (append (list 'or)
                                  (cdr lst))
                          (cadr lst)))
                (xor-all-macro (cdr lst)))
          (car lst))
      nil))

(defmacro xor-all (&rest args)
  (xor-all-macro args))

;;;;;;;;;;;;;;;;;
;; DEFUN-TYPED ;;
;;;;;;;;;;;;;;;;;

#|

Example 1 (general):

(defun-typed foo :C (x :A y :B)
  <definition>)

=>

(defun foo (x y)
  (declare (xargs :guard (and (A x)
                              (B y))))
  <definition>)

(defthm-guarded foo-type-constraint
    (implies (and (A x)
                  (B y))
             (C (foo x y))))

Example 2 (specific):

(defun-typed between :type booleanp (x :type integerp 
                                     y :type integerp 
                                     z :type integerp)
  (and (<= x y) (<= y z)))

=>

(defun between (x y z)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (integerp z))))
  (and (<= x y) (<= y z)))

(defthm-guarded between-type-constraint
    (implies (and (integerp x)
                  (integerp y)
                  (integerp z))
             (booleanp (between x y z))))

|#

(defun typed-arg-listp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (cdr x))
           (equal (cadr x) ':type)
           (consp (cddr x))
           (typed-arg-listp (cdddr x)))))

(defun get-args (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (cond ((endp typed-args) nil)
        ((endp (cdr typed-args)) nil)
        ((endp (cddr typed-args)) nil)
        (t (cons (car typed-args)
                 (get-args (cdddr typed-args))))))

(defun get-types (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (cond ((endp typed-args) nil)
        ((endp (cdr typed-args)) nil)
        ((endp (cddr typed-args)) nil)
        (t (cons (caddr typed-args)
                 (get-types (cdddr typed-args))))))

(defun get-type-constraint-1 (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (cond ((endp typed-args) nil)
        ((endp (cdr typed-args)) nil)
        ((endp (cddr typed-args)) nil)
        ((equal (caddr typed-args) ':all)
         (get-type-constraint-1 (cdddr typed-args)))
        (t (cons (list (caddr typed-args) (car typed-args))
                 (get-type-constraint-1 (cdddr typed-args))))))

(defun get-type-constraint (typed-args)
  (let ((gtc-1 (get-type-constraint-1 typed-args)))
    (cond ((atom gtc-1) t)
          ((atom (cdr gtc-1)) (car gtc-1))
          (t (cons 'and gtc-1)))))

(defun type-constraint-name (name)
  (intern (string-append (string name) "-TYPE-CONSTRAINT") "ACL2"))

(defmacro defun-typed (name type-kwd type typed-args &rest rst)
  (declare (xargs :guard (equal type-kwd ':type))
           (ignore type-kwd))
  (list 'progn
        (append (list 'defun name (get-args typed-args)
                      (list 'declare 
                            (list 'xargs 
                                  :guard 
                                  (get-type-constraint typed-args))))
              rst)
        (list 'defthm-guarded (type-constraint-name name)
              (list 'implies 
                    (get-type-constraint typed-args)
                    (list type (cons name (get-args typed-args)))))))

;;;;;;;;;;;;;;;;;;
;; DEFCOPRODUCT ;;
;;;;;;;;;;;;;;;;;;

#|
(defcoproduct BList
    (BNil)
    (BCons booleanp BList))

=>

(defun-typed BList (data)
  ...)

(defun-typed BCons (data)
  (and (consp data)
       ...))

|#

(defun nthcdr-macro (n x)
  (if (zp n)
      x
      (list 'cdr (nthcdr-macro (1- n) x))))

(defmacro nthcdr-ex (n x)
  (nthcdr-macro n x))

(defun type-case-macro-1 (rst n)
  (if (atom rst)
      nil
      (cond ((equal (caddr rst) ':all)
             (cons (list 'consp (list 'nthcdr-ex n 'data))
                   (type-case-macro-1 (cdddr rst) (1+ n))))
            (t 
             (append (list (list 'consp (list 'nthcdr-ex n 'data))
                           (list (caddr rst) (list 'car (list 'nthcdr-ex n 'data))))
                     (type-case-macro-1 (cdddr rst) (1+ n)))))))

(defun type-case-macro (type-case rst)
  (append (list 'and 
                (list 'equal 
                      (list 'car 'data)
                      (list 'quote type-case)))
          (type-case-macro-1 rst 1)))

(defun map-type-case-macro (l)
  (if (atom l)
      nil
      (cons (type-case-macro (caar l) (cdar l))
            (map-type-case-macro (cdr l)))))

(defun add-p-to-name (name)
  (intern (string-append (string name) "P") "ACL2"))

(defun type-case-def-macro (type-case rst)
  (list 'defun-typed
        (add-p-to-name type-case)
        ':type
        'booleanp
        (list 'data ':type ':all)
        (append (list 'and
                      (list 'consp 'data)
                      (list 'equal
                            (list 'car 'data)
                            (list 'quote type-case)))
                (type-case-macro-1 rst 1))))

(defun map-type-case-def-macro (l)
  (if (atom l)
      nil
      (cons (type-case-def-macro (caar l) (cdar l))
            (map-type-case-def-macro (cdr l)))))

(defun construct-type-case-macro (type type-case rst)
  (list 'defun-typed
        type-case
        ':type
        (add-p-to-name type)
        rst
        (append (list 'list
                      `(quote ,type-case))
                (get-args rst))))

(defun map-construct-type-case-macro (type l)
  (if (atom l)
      nil
    (cons (construct-type-case-macro type (caar l) (cdar l))
          (map-construct-type-case-macro type (cdr l)))))

(defun add-type-union-to-name (name)
  (intern (string-append (string name) "-TYPE-UNION") "ACL2"))

(defun assert-one-of-type-cases-macro-1 (type-cases)
  (if (atom type-cases)
      nil
    (cons (list (add-p-to-name (caar type-cases)) '(quote data))
          (assert-one-of-type-cases-macro-1 (cdr type-cases)))))

(defun assert-one-of-type-cases-macro (type-cases)
  (cons 'xor-all (assert-one-of-type-cases-macro-1 type-cases)))

(defmacro defcoproduct (type &rest type-cases)
  (append 
   (list 'progn
         (list 'defun-typed
               (add-p-to-name type)
               ':type
               'booleanp
               (list 'data ':type ':all)
               (list 'and
                     (list 'consp 'data)
                     (cons 'or (map-type-case-macro type-cases)))))
   (map-type-case-def-macro type-cases)
   (map-construct-type-case-macro type type-cases)
   (list (list 'defthm
               (add-type-union-to-name type)
               (list 'equal 
                     (list (add-p-to-name type)
                           '(quote data))
                     (assert-one-of-type-cases-macro type-cases))))))
