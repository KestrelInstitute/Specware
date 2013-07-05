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

;;;;;;;;;;;;;;;;;
;; DEFUN-TYPED ;;
;;;;;;;;;;;;;;;;;

;; Example 1 (general):

;; (defun-typed foo :C (x :A y :B)
;;   <definition>)

;; =>

;; (defun foo (x y)
;;   (declare (xargs :guard (and (A x)
;;                               (B y))))
;;   <definition>)

;; (defthm-guarded foo-type-constraint
;;     (implies (and (A x)
;;                   (B y))
;;              (C (foo x y))))

;; Example 2 (specific):

;; (defun-typed between :type booleanp (x :type integerp 
;;                                      y :type integerp 
;;                                      z :type integerp)
;;   (and (<= x y) (<= y z)))

;; =>

;; (defun between (x y z)
;;   (declare (xargs :guard (and (integerp x)
;;                               (integerp y)
;;                               (integerp z))))
;;   (and (<= x y) (<= y z)))

;; (defthm-guarded between-type-constraint
;;     (implies (and (integerp x)
;;                   (integerp y)
;;                   (integerp z))
;;              (booleanp (between x y z))))

(defun add-p-to-name (name)
  (intern (string-append (string name) "P") "ACL2"))

(defun hyphenate-symbols-string (syms)
  (cond ((atom syms) "")
        ((atom (cdr syms)) (string (car syms)))
        (t (string-append (string-append (string (car syms))
                                         "-")
                          (hyphenate-symbols-string (cdr syms))))))

(defun hyphenate-symbols (syms)
  (intern (hyphenate-symbols-string syms) "ACL2"))

(defun integer-to-string (n)
  (declare (xargs :mode :program))
  (subseq (fms-to-string "~s0" (list (cons #\0 n))
                         :fmt-control-alist nil)
          1 nil))

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

(mutual-recursion
 (defun match-conditions (pattern var-name)
   (declare (xargs :mode :program))
   (cond ((atom pattern) nil)
         (t
          (cons (list (add-p-to-name (car pattern)) var-name)
                (subterm-match-conditions-1 (car pattern) 
                                            (cdr pattern) 
                                            var-name 
                                            1)))))
 
 (defun subterm-match-conditions-1 (constructor-name arg-patterns var-name n)
   (declare (xargs :mode :program))
   (cond ((atom arg-patterns) nil)
         (t (append (match-conditions 
                     (car arg-patterns)
                     (list (hyphenate-symbols 
                            (list constructor-name
                                  (intern (string-append 
                                           "ARG"
                                           (integer-to-string n))
                                          "ACL2")))
                           var-name))
                    (subterm-match-conditions-1 constructor-name
                                                (cdr arg-patterns)
                                                var-name
                                                (1+ n)))))))

(defun match-condition (pattern var-name)
  (declare (xargs :mode :program))
  (cons 'and (match-conditions pattern var-name)))

(mutual-recursion
 (defun bindings (pattern term)
   (cond ((equal pattern '_) nil)
         ((symbolp pattern) (list (list pattern term)))
         ((atom pattern) nil)
         (t (subterm-bindings-1 (car pattern) (cdr pattern) term 1))))

 (defun subterm-bindings-1 (constructor-name arg-patterns var-name n)
   (declare (xargs :mode :program))
   (cond ((atom arg-patterns) nil)
         (t (append (bindings 
                     (car arg-patterns)
                     (list (hyphenate-symbols 
                            (list constructor-name
                                  (intern (string-append 
                                           "ARG"
                                           (integer-to-string n))
                                          "ACL2")))
                           var-name))
                    (subterm-bindings-1 constructor-name
                                        (cdr arg-patterns)
                                        var-name
                                        (1+ n)))))))

(defun case-to-cond-1 (var-name cases)
  (declare (xargs :mode :program))
  (cond ((atom cases) nil)
        (t 
         (let* ((pattern (caar cases))
                (term (cadar cases)))
           (cons (list
                  (match-condition pattern var-name)
                  (let ((b (bindings pattern var-name)))
                    (if (atom b)
                        term
                        (list 'let (bindings pattern var-name) term))))
                 (case-to-cond-1 var-name (cdr cases)))))))

(defun case-to-cond (var-name cases)
  (declare (xargs :mode :program))
  (cons 'cond (case-to-cond-1 var-name cases)))

(defun case-to-cond-macro (term)
  (declare (xargs :mode :program))
  (cond ((atom term) term)
        ((equal (car term) 'case-of)
         (case-to-cond (cadr term) (cddr term)))
        (t term)))

(defmacro defun-typed (name type-kwd type typed-args dfn); &rest rst)
  (declare (xargs :guard (equal type-kwd ':type))
           (ignore type-kwd))
  (append (list 'progn
                (append (list 'defun name (get-args typed-args)
                              (list 'declare 
                                    (list 'xargs 
                                          :guard 
                                          (get-type-constraint typed-args)
                                          :verify-guards
                                          nil)))
                        (list (case-to-cond-macro dfn))))
          (if (equal type ':all)
              nil
              (let ((term (list 'implies
                                (get-type-constraint typed-args)
                                (list type (cons name (get-args
                                                       typed-args))))))
                (list 
                 (list 'defthm (type-constraint-name name) 
                       (implies-to-implies-macro term)
                       ':rule-classes 
                       (list (list ':rewrite
                                   ':corollary
                                   term
                                   ':hints
                                   (list (list '"Goal" 
                                               ':in-theory 
                                               (list 'theory '(quote minimal-theory))))))))))
          (list (list 'verify-guards name))
          (list (list 'verify-guards (type-constraint-name name)))))


;;;;;;;;;;;;;;;;;;
;; DEFCOPRODUCT ;;
;;;;;;;;;;;;;;;;;;

#|
(defcoproduct type-name
    <type-case> = (constructor-name arg1 :type arg1-type
                                    arg2 :type arg2-type
                                    ...)
    <type-case>
    <type-case>)

|#

(defun add-type-union-to-name (name)
  (intern (string-append (string name) "-TYPE-UNION") "ACL2"))

(defun nthcdr-macro (n x)
  (if (zp n)
      x
      (list 'cdr (nthcdr-macro (1- n) x))))

(defmacro nthcdr-ex (n x)
  (nthcdr-macro n x))

(defun type-case-macro-1 (rst n)
  (if (atom rst)
      (list (list 'equal (list 'nthcdr-ex n 'data) 'nil))
      (cond ((equal (caddr rst) ':all)
             (cons (list 'consp (list 'nthcdr-ex n 'data))
                   (type-case-macro-1 (cdddr rst) (1+ n))))
            (t 
             (append (list (list 'consp (list 'nthcdr-ex n 'data))
                           (list (caddr rst) (list 'car (list 'nthcdr-ex n 'data))))
                     (type-case-macro-1 (cdddr rst) (1+ n)))))))

;; Produces a list of requirements for a type case.
;; Omits the "consp" requirement, as that always has to be at the top level.
(defun type-case-macro (constructor-name rst-type-case)
  (append (list 'and 
                (list 'equal 
                      (list 'car 'data)
                      (list 'quote constructor-name)))
          (type-case-macro-1 rst-type-case 1)))

;; Given the list of type-cases, gives a list of the requirements for each type
;; case. This is not a valid term by itself; it is to be or-ed for the type
;; definition.
(defun map-type-case-macro (type-cases)
  (if (atom type-cases)
      nil
      (cons (type-case-macro (caar type-cases) (cdar type-cases))
            (map-type-case-macro (cdr type-cases)))))

;; Given a type case name and the list of type requirements for its arguments,
;; produces the type case recognizer for that particular case.
(defun type-case-def-macro (constructor-name rst-type-case)
  (list 'defun-typed
        (add-p-to-name constructor-name)
        ':type
        'booleanp
        (list 'data ':type ':all)
        (append (list 'and
                      (list 'consp 'data)
                      (list 'equal
                            (list 'car 'data)
                            (list 'quote constructor-name)))
                (type-case-macro-1 rst-type-case 1))))

;; Given the list of type-cases, gives a list of "defun-typed"s, a recognizer
;; function for each individual case.
(defun map-type-case-def-macro (type-cases)
  (if (atom type-cases)
      nil
      (cons (type-case-def-macro (caar type-cases) (cdar type-cases))
            (map-type-case-def-macro (cdr type-cases)))))

;; Given the overall type-name, the constructor-name, and the list of type
;; requirements for this type case, produces a defun-typed for the constructor
;; of this type case.
(defun construct-type-case-macro (type-name constructor-name rst-type-case)
  (list 'defun-typed
        constructor-name
        ':type
        (add-p-to-name type-name)
        rst-type-case
        (append (list 'list
                      `(quote ,constructor-name))
                (get-args rst-type-case))))

;; Maps construct-type-case-macro over the type-cases for this type.
(defun map-construct-type-case-macro (type-name type-cases)
  (if (atom type-cases)
      nil
      (cons (construct-type-case-macro type-name (caar type-cases) (cdar type-cases))
            (map-construct-type-case-macro type-name (cdr type-cases)))))

(defun or-type-cases-macro-1 (type-cases)
  (if (atom type-cases)
      nil
      (cons (list (add-p-to-name (caar type-cases)) 'data)
            (or-type-cases-macro-1 (cdr type-cases)))))

;; Given the list of type-cases, produces a term asserting that data is exactly
;; one of these cases.
(defun one-hot-type-cases-macro (type-cases)
  (cons 'one-hot (or-type-cases-macro-1 type-cases)))

;; Given a type case name, an argument name, an argument type, and the position
;; of the argument in the type case, produces a destructor for that particular
;; argument.
(defun type-destructor-macro (type-case-name arg-name arg-type n)
  (list 'defun-typed
        arg-name
        ':type
        arg-type
        (list 'data ':type type-case-name)
        (list 'car (list 'nthcdr-ex n 'data))))

(defun type-case-destructors-macro-1 (case-type rst n)
  (cond ((atom rst) nil)
        (t (cons (type-destructor-macro case-type
                                        (car rst)
                                        (caddr rst)
                                        n)
                 (type-case-destructors-macro-1 case-type
                                                (cdddr rst)
                                                (1+ n))))))

;; Given the type case name and the list of args for the type case, produces a
;; list of destructor definitions for each arg in the type case.
(defun type-case-destructors-macro (type-case-name rst-type-case)
  (type-case-destructors-macro-1 type-case-name rst-type-case 1))

;; Given a list of type-cases, produces a list of destructor definitions for
;; each argument, for each type case.
(defun destructors-macro (type-cases)
  (cond ((atom type-cases) nil)
        (t (append (type-case-destructors-macro (add-p-to-name (caar type-cases))
                                                (cdar type-cases))
                   (destructors-macro (cdr type-cases))))))

(defun decons-cons-macro (deconstructor-name constructor-name rst-type-case)
  (list 'defthm-guarded
        (intern (string-append (string deconstructor-name)
                               (string-append 
                                "-"
                                (string constructor-name)))
                "ACL2")
        (list 'implies 
              (get-type-constraint rst-type-case)
              (list 'equal
                    (list deconstructor-name
                          (cons constructor-name
                                (get-args rst-type-case)))
                    deconstructor-name))))

(defun type-case-decons-cons-macro-1 (constructor-name
                                      type-case-args rst-type-case-args)
  (cond ((atom rst-type-case-args) nil)
        (t (cons (decons-cons-macro (car rst-type-case-args)
                                    constructor-name
                                    type-case-args)
                 (type-case-decons-cons-macro-1 constructor-name type-case-args
                                                (cdddr rst-type-case-args))))))

(defun type-case-decons-cons-macro (type-case)
  (type-case-decons-cons-macro-1 (car type-case)
                                 (cdr type-case)
                                 (cdr type-case)))

(defun type-decons-cons-macro (type-cases)
  (cond ((atom type-cases) nil)
        (t (append (type-case-decons-cons-macro (car type-cases))
                   (type-decons-cons-macro (cdr type-cases))))))

(defun pair-list-with-atom (lst atm)
  (if (atom lst)
      nil
      (cons (list (car lst) atm) (pair-list-with-atom (cdr lst) atm))))

(defun cons-decons-macro (constructor-name rst-type-case)
  (list 'defthm-guarded
        (if (atom rst-type-case)
            (hyphenate-symbols (list constructor-name 'one))
            (hyphenate-symbols (cons constructor-name
                                     (get-args rst-type-case))))
        (list 'implies
              (list (add-p-to-name constructor-name) 'data)
              (list 'equal
                    (cons constructor-name
                          (pair-list-with-atom 
                           (get-args rst-type-case)
                           'data))
                    'data))))

(defun map-cons-decons-macro (type-cases)
  (cond ((atom type-cases) nil)
        (t (cons (cons-decons-macro (caar type-cases) (cdar type-cases))
                 (map-cons-decons-macro (cdr type-cases))))))

(defun constructor-is-type-macro (type-name constructor-name)
  (list 'defthm-guarded
        (hyphenate-symbols (list constructor-name
                                 'is
                                 type-name))
        (list 'implies 
              (list (add-p-to-name constructor-name) 'data)
              (list (add-p-to-name type-name) 'data))))

(defun map-constructor-is-type-macro (type-name type-cases)
  (cond ((atom type-cases) nil)
        (t (cons (constructor-is-type-macro type-name (caar type-cases))
                 (map-constructor-is-type-macro type-name (cdr type-cases))))))

;; Destructor-measure-theorems
(defun destruct-measure-macro (constructor-name destructor-name)
  (list 'defthm
        (hyphenate-symbols (list destructor-name 'acl2-count))
        (list 'implies
              (list (add-p-to-name constructor-name) 'data)
              (list '< 
                    (list 'acl2-count (list destructor-name 'data))
                    (list 'acl2-count 'data)))))

(defun type-case-destruct-measure-macro (constructor-name rst-type-case)
  (cond ((atom rst-type-case) nil)
        (t (cons (destruct-measure-macro constructor-name (car rst-type-case))
                 (type-case-destruct-measure-macro constructor-name 
                                                   (cdddr rst-type-case))))))

(defun map-type-case-destruct-measure-macro (type-cases)
  (cond ((atom type-cases) nil)
        (t (append (type-case-destruct-measure-macro (caar type-cases)
                                                     (cdar type-cases))
                   (map-type-case-destruct-measure-macro (cdr type-cases))))))

;; One-hot theorems
(defun not-all-elim-macro (x)
  (cond ((atom x) nil)
        (t (cons (list 'not (list (add-p-to-name (car x)) 'data)) 
                 (not-all-elim-macro (cdr x))))))

(defun type-case-elim-macro (type-name constructor-name
                             other-constructor-names)
  (list 'defthm-guarded
        (hyphenate-symbols (list type-name constructor-name 'elim))
        (list 'implies 
              (append (list 'and
                            (list (add-p-to-name type-name) 'data))
                      (not-all-elim-macro other-constructor-names))
              (list (add-p-to-name constructor-name) 'data))))

(defun map-type-case-elim-macro-1 (type-name rst-constructor-names
                                   constructor-names)
  (cond ((atom rst-constructor-names) nil)
        (t (cons (type-case-elim-macro type-name 
                                       (car rst-constructor-names)
                                       (remove (car rst-constructor-names)
                                               constructor-names))
                 (map-type-case-elim-macro-1 type-name
                                             (cdr rst-constructor-names)
                                             constructor-names)))))

(defun map-type-case-elim-macro (type-name constructor-names)
  (map-type-case-elim-macro-1 type-name constructor-names constructor-names))

(defun cars (l)
  (cond ((atom l) nil)
        (t (cons (caar l) (cars (cdr l))))))

;; constructorp-constructor

(defun constructorp-constructor-macro (constructor-name rst-type-case)
  (list 'defthm-guarded 
        (hyphenate-symbols (list (add-p-to-name constructor-name) 
                                 constructor-name))
        (list 'implies
              (get-type-constraint rst-type-case)
              (list (add-p-to-name constructor-name)
                    (cons constructor-name (get-args rst-type-case))))))

(defun map-constructorp-constructor-macro (type-cases)
  (cond ((atom type-cases) nil)
        (t (cons (constructorp-constructor-macro (caar type-cases)
                                                 (cdar type-cases))
                 (map-constructorp-constructor-macro (cdr type-cases))))))

;; type cases don't overlap
(defun not-constructorp-constructor-macro (not-constructor-name
                                           constructor-name rst-type-case)
  (list 'defthm-guarded
        (hyphenate-symbols (list constructor-name
                                 'not 
                                 (add-p-to-name not-constructor-name)))
        (list 'implies
              (get-type-constraint rst-type-case)
              (list 'not (list (add-p-to-name not-constructor-name)
                               (cons constructor-name (get-args
                                                       rst-type-case)))))))

(defun map-not-constructorp-constructor-macro (not-constructor-names
                                               constructor-name rst-type-case)
  (cond ((atom not-constructor-names) nil)
        (t (cons (not-constructorp-constructor-macro 
                  (car not-constructor-names)
                  constructor-name rst-type-case)
                 (map-not-constructorp-constructor-macro
                  (cdr not-constructor-names)
                  constructor-name rst-type-case)))))

(defun map-map-not-constructorp-constructor-macro-1 (constructor-names
                                                     type-cases)
  (cond ((atom type-cases) nil)
        (t (append (map-not-constructorp-constructor-macro
                    (remove (caar type-cases) constructor-names)
                    (caar type-cases)
                    (cdar type-cases))
                   (map-map-not-constructorp-constructor-macro-1
                    constructor-names (cdr type-cases))))))

(defun map-map-not-constructorp-constructor-macro (type-cases)
  (map-map-not-constructorp-constructor-macro-1 (cars type-cases) type-cases))

(defun uniqueness-macro (constructor-name)
  (list 'defthm
        (hyphenate-symbols (list constructor-name 'unique))
        (list 'implies
              (list 'and 
                    (list (add-p-to-name constructor-name) 'data1)
                    (list (add-p-to-name constructor-name) 'data2))
              (list 'equal
                    (list 'equal 'data1 'data2)
                    t))))

(defun map-uniqueness-macro (type-cases)
  (cond ((atom type-cases) nil)
        (t (if (consp (cdar type-cases))
               (map-uniqueness-macro (cdr type-cases))
               (cons (uniqueness-macro (caar type-cases))
                     (map-uniqueness-macro (cdr type-cases)))))))

(defun typep-consp (type-name)
  (list 'defthm 
        (hyphenate-symbols (list (add-p-to-name type-name)
                                 'consp))
        (list 'implies
              (list (add-p-to-name type-name) 'data)
              (list 'consp 'data))))

(defun get-predicates-1 (type-cases)
  (cond ((atom type-cases) nil)
        (t (cons (add-p-to-name (caar type-cases))
                 (get-predicates-1 (cdr type-cases))))))

(defun get-predicates (type-name type-cases)
  (cons (add-p-to-name type-name)
        (get-predicates-1 type-cases)))

(defun get-constructors (type-cases)
  (cond ((atom type-cases) nil)
        (t (cons (caar type-cases) (get-constructors (cdr type-cases))))))

(defun get-destructors-type-case (rst-type-case)
  (cond ((atom rst-type-case) nil)
        (t (cons (car rst-type-case) 
                 (get-destructors-type-case (cdddr rst-type-case))))))

(defun get-destructors (type-cases)
  (cond ((atom type-cases) nil)
        (t (append (get-destructors-type-case (cdar type-cases))
                   (get-destructors (cdr type-cases))))))

(defmacro defcoproduct-explicit-destructor-names (type &rest type-cases)
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
   (list (typep-consp type))
   (map-type-case-def-macro type-cases)
   (map-constructor-is-type-macro type type-cases)
   (map-construct-type-case-macro type type-cases)
   (destructors-macro type-cases)
   (type-decons-cons-macro type-cases)
   (map-cons-decons-macro type-cases)
   (map-type-case-destruct-measure-macro type-cases)
   (map-type-case-elim-macro type (cars type-cases))
   (map-constructorp-constructor-macro type-cases)
   (map-map-not-constructorp-constructor-macro type-cases)
   (map-uniqueness-macro type-cases) ;; TODO: generalize this
   (list (list 'deftheory
               (hyphenate-symbols (list type 'types))
               (list 'quote (get-predicates type type-cases))))
   (list (list 'deftheory
               (hyphenate-symbols (list type 'constructors))
               (list 'quote (get-constructors type-cases))))
   (list (list 'deftheory
               (hyphenate-symbols (list type 'destructors))
               (list 'quote (get-destructors type-cases))))
   (list (list 'in-theory 
               (list 'disable (hyphenate-symbols 
                               (list type 'types)))))
   (list (list 'in-theory 
               (list 'disable (hyphenate-symbols 
                               (list type 'constructors)))))
   (list (list 'in-theory 
               (list 'disable (hyphenate-symbols 
                               (list type 'destructors)))))))

(defun integer-to-string (n)
  (declare (xargs :mode :program))
  (subseq (fms-to-string "~s0" (list (cons #\0 n))
                         :fmt-control-alist nil)
          1 nil))

(defun transform-type-case-1 (constructor-name rst-type-case n)
  (declare (xargs :mode :program))
  (cond ((atom rst-type-case) nil)
        ((atom (car rst-type-case))
         (append
          (list (hyphenate-symbols 
                 (list constructor-name
                       (intern (string-append "ARG" 
                                              (integer-to-string n)) 
                               "ACL2")))
                ':type
                (car rst-type-case))
          (transform-type-case-1 constructor-name (cdr rst-type-case) (1+ n))))
        (t (append (list (cadar rst-type-case) ':type (caar rst-type-case))
                   (transform-type-case-1 constructor-name 
                                          (cdr rst-type-case)
                                          (1+ n))))))

(defun transform-type-case (constructor-name rst-type-case)
  (declare (xargs :mode :program))
  (cons constructor-name 
        (transform-type-case-1 constructor-name 
                               rst-type-case
                               1)))

(defun map-transform-type-case (type-cases)
  (declare (xargs :mode :program))
  (cond ((atom type-cases) nil)
        (t (cons (transform-type-case (caar type-cases)
                                      (cdar type-cases))
                 (map-transform-type-case (cdr type-cases))))))

(defun defcoproduct-macro (type type-cases)
  (declare (xargs :mode :program))
  (append (list 'defcoproduct-explicit-destructor-names
                type)
          (map-transform-type-case type-cases)))

(defmacro defcoproduct (type &rest type-cases)
  (defcoproduct-macro type type-cases))
