(in-package "ACL2")

(include-book "tools/defsum" :dir :system)

(defmacro implies-macro (x y)
  (declare (xargs :guard t))
  (list 'if x (list 'if y 't 'nil) 't))

(mutual-recursion

 (defun implies-to-implies-macro (term)
   (declare (xargs :guard t))
   (if (atom term) 
       term
       (let ((fn-name (if (equal (car term) 'implies) 
                          'implies-macro 
                          (car term))))
         (cons fn-name (map-implies-to-implies-macro (cdr term))))))

 (defun map-implies-to-implies-macro (terms)
   (declare (xargs :guard t))
   (if (atom terms)
       nil
       (cons (implies-to-implies-macro (car terms))
             (map-implies-to-implies-macro (cdr terms))))))

(defun lookup-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (consp (cdr x))
                (lookup-listp (cddr x))))))

(defun lookup (x l)
  (declare (xargs :guard (lookup-listp l)))
  (if (mbt (lookup-listp l))
      (cond ((atom l) nil)
            ((equal (car l) x) (cadr l))
            (t (lookup x (cddr l))))
      nil))

;;;;;;;;;;;;;;;;;
;; DEFUN-TYPED ;;
;;;;;;;;;;;;;;;;;

;; Use:
;;
;; (defun-typed example ((x type1-p)
;;                       (y type2-p)
;;                       (z type3-p)
;;                       (a type4-p)
;;                       (b type5-p)
;;                       (c type6-p)
;;                       (i type7-p)
;;                       (j type8-p))
;;              output-type-p
;;   (declare (ignore a b c)
;;            (type integer i j)
;;            (xargs :guard (symbolp x)
;;                   :measure (- i j)
;;                   :ruler-extenders :basic
;;                   :well-founded-relation my-wfr
;;                   :hints (("Goal"
;;                            :do-not-induct t
;;                            :do-not '(generalize fertilize)
;;                            :expand ((assoc x a) (member y z))
;;                            :restrict ((<-trans ((x x) (y (foo x)))))
;;                            :hands-off (length binary-append)
;;                            :in-theory (set-difference-theories
;;                                        (current-theory :here)
;;                                        '(assoc))
;;                            :induct (and (nth n a) (nth n b))
;;                            :use ((:instance assoc-of-append
;;                                             (x a) (y b) (z c))
;;                                  (:functional-instance
;;                                   (:instance p-f (x a) (y b))
;;                                   (p consp)
;;                                   (f assoc)))))
;;                   :guard-hints (("Subgoal *1/3'"
;;                                  :use ((:instance assoc-of-append
;;                                                   (x a) (y b) (z c)))))
;;                   :mode :logic
;;                   :normalize nil
;;                   :non-executable t
;;                   :otf-flg t
;;                   :type-constraint-lemmas 
;;                    ((defthm example-type-constraint-lemma1 ...)
;;                     (defthm example-type-constraint-lemma2 ...))
;;                   :type-constraint-args
;;                   (:rule-classes foo1
;;                    :instructions foo2
;;                    :hints foo3
;;                    :otf-flg foo4
;;                    :doc foo5))
;;   (example-body x y z i j))
;;
;;  =>
;;
;; (defun example (x y z a b c i j
;;   (declare (ignore a b c)
;;            (type integer i j)
;;            (xargs :guard (and (type1-p x)
;;                               (type2-p y)
;;                               (type3-p z)
;;                               (type4-p a)
;;                               (type5-p b)
;;                               (type6-p c)
;;                               (type7-p i)
;;                               (type8-p j))
;;                   :verify-guards nil
;;                   :guard (symbolp x)
;;                   :measure (- i j)
;;                   :ruler-extenders :basic
;;                   :well-founded-relation my-wfr
;;                   :hints (("Goal"
;;                            :do-not-induct t
;;                            :do-not '(generalize fertilize)
;;                            :expand ((assoc x a) (member y z))
;;                            :restrict ((<-trans ((x x) (y (foo x)))))
;;                            :hands-off (length binary-append)
;;                            :in-theory (set-difference-theories
;;                                        (current-theory :here)
;;                                        '(assoc))
;;                            :induct (and (nth n a) (nth n b))
;;                            :use ((:instance assoc-of-append
;;                                             (x a) (y b) (z c))
;;                                  (:functional-instance
;;                                   (:instance p-f (x a) (y b))
;;                                   (p consp)
;;                                   (f assoc)))))
;;                   :guard-hints (("Subgoal *1/3'"
;;                                  :use ((:instance assoc-of-append
;;                                                   (x a) (y b) (z c)))))
;;                   :mode :logic
;;                   :normalize nil
;;                   :non-executable t
;;                   :otf-flg t
;;   (if (mbt (and (type1-p x)
;;                 (type2-p y)
;;                 (type3-p z)
;;                 (type4-p a)
;;                 (type5-p b)
;;                 (type6-p c)
;;                 (type7-p i)
;;                 (type8-p j)))
;;       (example-body x y z i j)
;;       nil))
;;
;; (defthm example-type-constraint-lemma1 ...)
;; (defthm example-type-constraint-lemma2 ...)
;;
;; (defthm example-type-constraint
;;   (implies (and (type1-p x)
;;                 (type2-p y)
;;                 (type3-p z)
;;                 (type4-p a)
;;                 (type5-p b)
;;                 (type6-p c)
;;                 (type7-p i)
;;                 (type8-p j)))
;;   :type-constraint-rule-classes foo1
;;   :type-constraint-instructions foo2
;;   :type-constraint-hints foo3
;;   :type-constraint-otf-flg foo4
;;   :type-constraint-doc foo5)


(defun add-p-to-name (name)
  (declare (xargs :guard (symbolp name)))
  (intern (string-append (string name) "P") "ACL2"))

(defun hyphenate-symbols-string (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (cond ((atom syms) "")
        ((atom (cdr syms)) (string (car syms)))
        (t (string-append (string-append (string (car syms))
                                         "-")
                          (hyphenate-symbols-string (cdr syms))))))

(defun hyphenate-symbols (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (intern (hyphenate-symbols-string syms) "ACL2"))

(defun integer-to-string (n)
  (declare (xargs :mode :program
                  :guard (integerp n)))
  (subseq (fms-to-string "~s0" (list (cons #\0 n))
                         :fmt-control-alist nil)
          1 nil))

(defun is-function-p (term)
  (declare (xargs :guard t))
  (or (atom term)
      (equal (car term) 'lambda)))

(defun type-p (x)
  (declare (xargs :guard t))
  (or (symbolp x)
      (and (consp x)
           (consp (cdr x))
           (consp (cddr x))
           (atom (cdddr x))
           (equal (car x) ':subtype)
           (symbolp (cadr x)))))

(defun typed-arg-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        ((atom (car x)) (typed-arg-listp (cdr x)))
        (t (and (consp (car x))
                (consp (cdar x))
                (atom (cddar x))
                (type-p (cadar x))
                (typed-arg-listp (cdr x))))))

(defun get-args (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (cond ((endp typed-args) nil)
        ((atom (car typed-args))
         (cons (car typed-args)
               (get-args (cdr typed-args))))
        (t (cons (caar typed-args)
                 (get-args (cdr typed-args))))))

(defun get-types (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (cond ((endp typed-args) nil)
        ((atom (car typed-args))
         (cons ':all (get-types (cdr typed-args))))
        (t (cons (cadar typed-args)
                 (get-types (cdr typed-args))))))

(defun get-type-constraint-1 (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (cond ((endp typed-args) nil)
        ((atom (car typed-args))
         (get-type-constraint-1 (cdr typed-args)))
        ((consp (second (first typed-args)))
         (let* ((arg-name (first (first typed-args)))
                (parent-type-p (second (second (first typed-args))))
                (restriction (third (second (first typed-args))))
                (restriction-term
                 (if (is-function-p restriction)
                     (list restriction arg-name)
                     restriction)))
           (cons (list parent-type-p arg-name)
                 (cons restriction-term
                       (get-type-constraint-1 (cdr typed-args))))))
        (t (cons (list (second (first typed-args)) (first (first typed-args)))
                 (get-type-constraint-1 (cdr typed-args))))))

(defun get-type-constraint (typed-args)
  (declare (xargs :guard (typed-arg-listp typed-args)))
  (let ((gtc-1 (get-type-constraint-1 typed-args)))
    (cond ((atom gtc-1) t)
          ((atom (cdr gtc-1)) (car gtc-1))
          (t (cons 'and gtc-1)))))

(defun lookup-declare (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) nil)
        ((atom (car l)) (lookup-declare (cdr l)))
        ((equal (caar l) 'declare)
         (car l))
        (t (lookup-declare (cdr l)))))

(defun remove-type-constraint-xargs-1 (xargs)
  (declare (xargs :guard (true-listp xargs)))
  (cond ((atom xargs) nil)
        ((equal (car xargs) ':type-constraint-lemmas)
         (remove-type-constraint-xargs-1 (cddr xargs)))
        ((equal (car xargs) ':type-constraint-args)
         (remove-type-constraint-xargs-1 (cddr xargs)))
        (t (cons (car xargs) 
                 (cons (cadr xargs) (remove-type-constraint-xargs-1
                                     (cddr xargs)))))))

;(defun remove-type-constraint-xargs (xargs typed-args)
;  (append (list ':guard (get-type-constraint typed-args)
;                ':verify-guards nil)
;          (remove-type-constraint-xargs-1 xargs)))

(defun remove-type-constraint-declare-1 (decl)
  (declare (xargs :guard (true-list-listp decl)))
  (cond ((atom decl) nil)
        ((equal (caar decl) 'xargs)
         (cons (cons 'xargs (remove-type-constraint-xargs-1 (cdar decl)))
               (remove-type-constraint-declare-1 (cdr decl))))
        (t (cons (car decl) (remove-type-constraint-declare-1 (cdr decl))))))

(defun remove-type-constraint-declare (decl)
  (declare (xargs :guard (or (null decl)
                             (and (consp decl)
                                  (equal (car decl) 'declare)
                                  (true-list-listp (cdr decl))))))
  (if decl
      (cons 'declare (remove-type-constraint-declare-1 (cdr decl)))
      nil))

(defun get-type-constraint-args-1 (xargs)
  (declare (xargs :guard (true-listp xargs)))
  (cond ((atom xargs) nil)
        ((equal (car xargs) ':type-constraint-args)
         (cadr xargs))
        (t (get-type-constraint-args-1 (cddr xargs)))))

(defun get-type-constraint-args-decl-1 (decl)
  (declare (xargs :guard (true-list-listp decl)))
  (cond ((atom decl) nil)
        ((equal (caar decl) 'xargs)
         (get-type-constraint-args-1 (cdar decl)))
        (t (get-type-constraint-args-decl-1 (cdr decl)))))

(defun get-type-constraint-args-decl (decl)
  (declare (xargs :guard (or (null decl)
                             (and (consp decl)
                                  (equal (car decl) 'declare)
                                  (true-list-listp (cdr decl))))))
  (if decl
      (get-type-constraint-args-decl-1 (cdr decl))
      nil))

(defun get-type-constraint-lemmas-1 (xargs)
  (declare (xargs :guard (true-listp xargs)))
  (cond ((atom xargs) nil)
        ((equal (car xargs) ':type-constraint-lemmas)
         (cadr xargs))
        (t (get-type-constraint-lemmas-1 (cddr xargs)))))

(defun get-type-constraint-lemmas-decl-1 (decl)
  (declare (xargs :guard (true-list-listp decl)))
  (cond ((atom decl) nil)
        ((equal (caar decl) 'xargs)
         (get-type-constraint-lemmas-1 (cdar decl)))
        (t (get-type-constraint-lemmas-decl-1 (cdr decl)))))

(defun get-type-constraint-lemmas-decl (decl)
  (declare (xargs :guard (or (null decl)
                             (and (consp decl)
                                  (equal (car decl) 'declare)
                                  (true-list-listp (cdr decl))))))
  (if decl
      (get-type-constraint-lemmas-decl-1 (cdr decl))
      nil))

(defun lookup-body (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((atom l) nil)
        ((keywordp (car l))
         (if (consp (cdr l))
             (lookup-body (cddr l))
             nil))
        ((and (consp (car l)) (equal (caar l) 'declare))
         (lookup-body (cdr l)))
        (t (car l))))

(defmacro defun-typed (name typed-args type &rest rst)
  (declare (xargs :guard (and (symbolp name)
                              (typed-arg-listp typed-args)
                              (type-p type)
                              (true-listp rst))))
  (let* ((decl (lookup-declare rst))
         (decl-defun (remove-type-constraint-declare decl))
         (type-constraint-args (get-type-constraint-args-decl decl))
         (type-constraint-lemmas (get-type-constraint-lemmas-decl decl))
         (body (lookup-body rst)))
    (append (list 'progn
                  (append (list 'defun name (get-args typed-args) 
                                (list 'declare
                                      (list 'xargs 
                                            ':guard 
                                            (get-type-constraint typed-args)
                                            ':verify-guards nil)))
                          (if decl-defun (list decl-defun) nil)
                          (if (equal (get-type-constraint typed-args) t)
                              (list body)
                              (list 
                               (list 'if
                                     (list 'mbt 
                                           (get-type-constraint typed-args))
                                     body
                                     nil)))))
            type-constraint-lemmas
            (cond ((equal type ':all) nil)
                  ((consp type) ; subtype
                   (let* ((parent-type (cadr type))
                          (restriction (caddr type))
                          (type-constraint (get-type-constraint typed-args))
                          (term 
                           (if (eq type-constraint t)
                               (list 'and
                                     (list parent-type (cons name (get-args
                                                                   typed-args)))
                                     (list restriction (cons name (get-args
                                                                   typed-args))))
                               (list 'implies
                                      (get-type-constraint typed-args)
                                      (list 
                                       'and
                                       (list parent-type (cons name (get-args
                                                                     typed-args)))
                                       (list restriction (cons name (get-args
                                                                     typed-args))))))))
                     (list
                      (append (list 'defthm 
                                    (hyphenate-symbols 
                                     (list name 'type-constraint))
                                    term)
                              type-constraint-args))))
                  (t (let* ((type-constraint (get-type-constraint typed-args))
                            (term
                             (if (eq type-constraint t)
                                 (list type (cons name (get-args typed-args)))
                                 (list 'implies
                                       (get-type-constraint typed-args)
                                       (list type (cons name (get-args
                                                              typed-args)))))))
                       (list 
                        (append (list 'defthm (hyphenate-symbols (list name 'type-constraint))
                                      term)
                                type-constraint-args)))))
;            (lookup ':guard-lemmas rst)
            (list (list 'verify-guards name)))))
;            (list (list 'verify-guards (hyphenate-symbols (list name 'type-constraint)))))))

;;;;;;;;;;;;;;;;;;
;; DEFPREDICATE ;;
;;;;;;;;;;;;;;;;;;

(defmacro defpredicate (name args &rest rst)
  (append (list 'defun-typed name (list (car args)) 'booleanp)
          rst))

;;;;;;;;;;;;;;;;
;; DEFSUBTYPE ;;
;;;;;;;;;;;;;;;;

;; (defsubtype subtype parenttype-p restriction)
;;
;; =>
;;
;; (defpredicate subtype-p ((parenttype-p x))
;;   (and (parenttype-p x)
;;        (restriction x)))

(defmacro defsubtype (subtype parenttype-p restriction)
  (list 'defpredicate
        subtype
        (list 'x)
        (list 'and (list parenttype-p 'x)
              (list restriction 'x))))

;;;;;;;;;;;;;;;;;;
;; DEFTHM-TYPED ;;
;;;;;;;;;;;;;;;;;;

;; Use:
;;
;; (defthm-typed the-theorem
;;   ((type1-p x) (type2-p y) (type3-p z))
;;   (implies (hyps x y z) (concl x y z))
;;   :rule-classes (:REWRITE :GENERALIZE)
;;   :instructions (induct prove promote (dive 1) x
;;                         (dive 2) = top (drop 2) prove)
;;   :hints (("Goal"
;;            :do-not '(generalize fertilize)
;;            :in-theory (set-difference-theories
;;                        (current-theory :here)
;;                        '(assoc))
;;            :induct (and (nth n a) (nth n b))
;;            :use ((:instance assoc-of-append
;;                             (x a) (y b) (z c))
;;                  (:functional-instance
;;                   (:instance p-f (x a) (y b))
;;                   (p consp)
;;                   (f assoc)))))
;;   :otf-flg t
;;   :doc "#0[one-liner/example/details]")
;;
;; =>
;;
;; (progn
;; (defthm the-theorem
;;     (implies (and (type1-p x)
;;                   (type2-p y)
;;                   (type3-p z)
;;                   (hyps x y z))
;;              (concl x y z))
;;   :rule-classes (:REWRITE :GENERALIZE)
;;   :instructions (induct prove promote (dive 1) x
;;                         (dive 2) = top (drop 2) prove)
;;   :hints (("Goal"
;;            :do-not '(generalize fertilize)
;;            :in-theory (set-difference-theories
;;                        (current-theory :here)
;;                        '(assoc))
;;            :induct (and (nth n a) (nth n b))
;;            :use ((:instance assoc-of-append
;;                             (x a) (y b) (z c))
;;                  (:functional-instance
;;                   (:instance p-f (x a) (y b))
;;                   (p consp)
;;                   (f assoc)))))
;;   :otf-flg t
;;   :doc "#0[one-liner/example/details]")
;; 
;; (defun-typed main-body ((type1-p x)
;;                         (type2-p y)
;;                         (type3-p z))
;;              booleanp
;;   (implies (hyps  x y z)
;;            (concl x y z))))

(defun flip-typed-vars (x)
  (cond ((atom x) nil)
        (t (cons (list (cadar x) (caar x))
                 (flip-typed-vars (cdr x))))))

(defmacro defthm-typed (name typed-vars term &rest rst)
  (list 'progn
        (list 'defun-typed
              (hyphenate-symbols (list name 'body))
              typed-vars
              'booleanp
              (implies-to-implies-macro term))
        (append (list 'defthm name 
                      (list 'implies 
                            (cons 'and (flip-typed-vars typed-vars))
                            term))
                rst)))

;;;;;;;;;;;;;;;;;;
;; DEFCOPRODUCT ;;
;;;;;;;;;;;;;;;;;;

(defun transform-type-case-1 (constructor-name rst-type-case n)
  (declare (xargs :mode :program))
  (cond ((atom rst-type-case) nil)
        ((atom (car rst-type-case))
         (cons
          (list (car rst-type-case)
                (hyphenate-symbols 
                 (list constructor-name
                       (intern (string-append "ARG" 
                                              (integer-to-string n)) 
                               "ACL2"))))
          (transform-type-case-1 constructor-name (cdr rst-type-case) (1+ n))))
        (t (cons (car rst-type-case) (transform-type-case-1 constructor-name
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
;  (append (list 'defcoproduct-explicit-destructor-names
  (append (list 'defsum
                type)
          (map-transform-type-case type-cases)))

(defmacro defcoproduct (type &rest type-cases)
  (defcoproduct-macro type type-cases))

(defun replace-_-with-& (x)
  (cond ((atom x) (if (equal x '_) '& x))
        (t (cons (replace-_-with-& (car x))
                 (replace-_-with-& (cdr x))))))

(defmacro case-of (term &rest clauses)
  (append (list 'pattern-match term)
          (replace-_-with-& clauses)))

(defmacro as-pattern-matcher
    (term args tests bindings lhses rhses pmstate)
  (cond ((not (true-listp args))
         (er hard 'pattern-match
             "badly formed expression: ~x0~%"
             (cons 'cons args)))
        (t ;; recursively pattern match all the args against copies of the term
         (let ((rhses (make-list-ac (len args) term rhses))
               (lhses (append args lhses)))
           (pattern-bindings-list lhses rhses tests bindings pmstate)))))


;;;;;;;;;;;;;;
;; BUILTINS ;;
;;;;;;;;;;;;;;

(defpredicate Int-p (x) (integerp x))
(defpredicate Bool-p (x) (booleanp x))
(defpredicate Nat-p (x) (natp x))
(defpredicate String-p (x) (stringp x))
(defun-typed int_+ ((x Int-p) (y Int-p))
             integerp
  (binary-+ x y))

;;;;;;;;;
;; OLD ;;
;;;;;;;;;

;(defun type-constraint-name (name)
;  (intern (string-append (string name) "-TYPE-CONSTRAINT") "ACL2"))

;; (mutual-recursion
;;  (defun match-conditions (pattern var-name)
;;    (declare (xargs :mode :program))
;;    (cond ((atom pattern) nil)
;;          ((equal (cadr pattern) '@)
;;           (cons (list (add-p-to-name (caddr pattern)) var-name)
;;                 (subterm-match-conditions-1 (caddr pattern)
;;                                             (cdddr pattern)
;;                                             var-name
;;                                             1)))
;;          (t
;;           (cons (list (add-p-to-name (car pattern)) var-name)
;;                 (subterm-match-conditions-1 (car pattern) 
;;                                             (cdr pattern) 
;;                                             var-name 
;;                                             1)))))

;;  (defun subterm-match-conditions-1 (constructor-name arg-patterns var-name n)
;;    (declare (xargs :mode :program))
;;    (cond ((atom arg-patterns) nil)
;;          (t (append (match-conditions 
;;                      (car arg-patterns)
;;                      (list (hyphenate-symbols 
;;                             (list constructor-name
;;                                   (intern (string-append 
;;                                            "ARG"
;;                                            (integer-to-string n))
;;                                           "ACL2")))
;;                            var-name))
;;                     (subterm-match-conditions-1 constructor-name
;;                                                 (cdr arg-patterns)
;;                                                 var-name
;;                                                 (1+ n)))))))

;; (defun match-condition (pattern var-name)
;;   (declare (xargs :mode :program))
;;   (cons 'and (match-conditions pattern var-name)))

;; (mutual-recursion
;;  (defun bindings (pattern term)
;;    (cond ((equal pattern '_) nil)
;;          ((symbolp pattern) (list (list pattern term)))
;;          ((atom pattern) nil)
;;          ((equal (cadr pattern) '@)
;;           (cons (list (car pattern) term) 
;;                 (subterm-bindings-1 (caddr pattern) 
;;                                     (cdddr pattern) 
;;                                     term 
;;                                     1)))
;;          (t (subterm-bindings-1 (car pattern) (cdr pattern) term 1))))

;;  (defun subterm-bindings-1 (constructor-name arg-patterns var-name n)
;;    (declare (xargs :mode :program))
;;    (cond ((atom arg-patterns) nil)
;;          (t (append (bindings 
;;                      (car arg-patterns)
;;                      (list (hyphenate-symbols 
;;                             (list constructor-name
;;                                   (intern (string-append 
;;                                            "ARG"
;;                                            (integer-to-string n))
;;                                           "ACL2")))
;;                            var-name))
;;                     (subterm-bindings-1 constructor-name
;;                                         (cdr arg-patterns)
;;                                         var-name
;;                                         (1+ n)))))))

;; (defun case-to-cond-1 (var-name cases)
;;   (declare (xargs :mode :program))
;;   (cond ((atom cases) nil)
;;         (t 
;;          (let* ((pattern (caar cases))
;;                 (term (cadar cases)))
;;            (cons (list
;;                   (match-condition pattern var-name)
;;                   (let ((b (bindings pattern var-name)))
;;                     (if (atom b)
;;                         term
;;                         (list 'let (bindings pattern var-name) term))))
;;                  (case-to-cond-1 var-name (cdr cases)))))))

;; (defun case-to-cond (var-name cases)
;;   (declare (xargs :mode :program))
;;   (cons 'cond (case-to-cond-1 var-name cases)))

;; (defun case-to-cond-macro (term)
;;   (declare (xargs :mode :program))
;;   (cond ((atom term) term)
;;         ((equal (car term) 'case-of)
;;          (case-to-cond (cadr term) (cddr term)))
;;         (t term)))


;(defun add-type-union-to-name (name)
;  (intern (string-append (string name) "-TYPE-UNION") "ACL2"))

;; (mutual-recursion 

;;  (defun coproduct-measure (x)
;;    (cond ((atom x) 0)
;;          (t (+ 1 (sum-coproduct-measure (cdr x))))))

;;  (defun sum-coproduct-measure (xs)
;;    (cond ((atom xs) 0)
;;          (t (+ (coproduct-measure (car xs))
;;                (sum-coproduct-measure (cdr xs)))))))

;; (defun nthcdr-macro (n x)
;;   (if (zp n)
;;       x
;;       (list 'cdr (nthcdr-macro (1- n) x))))

;; (defmacro nthcdr-ex (n x)
;;   (nthcdr-macro n x))

;; (defun type-case-macro-1 (rst n)
;;   (if (atom rst)
;;       (list (list 'equal (list 'nthcdr-ex n 'data) 'nil))
;;       (cond ((equal (car rst) ':all)
;;              (cons (list 'consp (list 'nthcdr-ex n 'data))
;;                    (type-case-macro-1 (cdr rst) (1+ n))))
;;             ((atom (car rst))
;;              (append (list (list 'consp (list 'nthcdr-ex n 'data))
;;                            (list (car rst) 
;;                                  (list 'car (list 'nthcdr-ex n 'data))))
;;                      (type-case-macro-1 (cdr rst) (1+ n))))
;;             ((equal (caar rst) ':all)
;;              (cons (list 'consp (list 'nthcdr-ex n 'data))
;;                    (type-case-macro-1 (cdr rst) (1+ n))))
;;             (t
;;              (append (list (list 'consp (list 'nthcdr-ex n 'data))
;;                            (list (caar rst) 
;;                                  (list 'car (list 'nthcdr-ex n 'data))))
;;                      (type-case-macro-1 (cdr rst) (1+ n)))))))

;; ;; Produces a list of requirements for a type case.
;; ;; Omits the "consp" requirement, as that always has to be at the top level.
;; (defun type-case-macro (constructor-name rst-type-case)
;;   (append (list 'and 
;;                 (list 'equal 
;;                       (list 'car 'data)
;;                       (list 'quote constructor-name)))
;;           (type-case-macro-1 rst-type-case 1)))

;; ;; Given the list of type-cases, gives a list of the requirements for each type
;; ;; case. This is not a valid term by itself; it is to be or-ed for the type
;; ;; definition.
;; (defun map-type-case-macro (type-cases)
;;   (if (atom type-cases)
;;       nil
;;       (cons (type-case-macro (caar type-cases) (cdar type-cases))
;;             (map-type-case-macro (cdr type-cases)))))

;; ;; Given a type case name and the list of type requirements for its arguments,
;; ;; produces the type case recognizer for that particular case.
;; (defun type-case-def-macro (constructor-name rst-type-case)
;;   (list 'defpredicate
;;         (add-p-to-name constructor-name)
;;         (list 'data)
;;         (append (list 'and
;;                       (list 'consp 'data)
;;                       (list 'equal
;;                             (list 'car 'data)
;;                             (list 'quote constructor-name)))
;;                 (type-case-macro-1 rst-type-case 1))))

;; ;; Given the list of type-cases, gives a list of "defun-typed"s, a recognizer
;; ;; function for each individual case.
;; (defun map-type-case-def-macro (type-cases)
;;   (if (atom type-cases)
;;       nil
;;       (cons (type-case-def-macro (caar type-cases) (cdar type-cases))
;;             (map-type-case-def-macro (cdr type-cases)))))

;; ;; Given the overall type-name, the constructor-name, and the list of type
;; ;; requirements for this type case, produces a defun-typed for the constructor
;; ;; of this type case.
;; (defun construct-type-case-macro (type-name constructor-name rst-type-case)
;;   (list 'defun-typed
;;         (list (add-p-to-name type-name) constructor-name)
;;         rst-type-case
;;         (append (list 'list
;;                       `(quote ,constructor-name))
;;                 (get-args rst-type-case))))

;; ;; Maps construct-type-case-macro over the type-cases for this type.
;; (defun map-construct-type-case-macro (type-name type-cases)
;;   (if (atom type-cases)
;;       nil
;;       (cons (construct-type-case-macro type-name (caar type-cases) (cdar type-cases))
;;             (map-construct-type-case-macro type-name (cdr type-cases)))))

;; ;; Given a type case name, an argument name, an argument type, and the position
;; ;; of the argument in the type case, produces a destructor for that particular
;; ;; argument.
;; (defun type-destructor-macro (type-case-name arg-name arg-type n)
;;   (list 'defun-typed
;;         (list arg-type arg-name)
;;         (list (list (add-p-to-name type-case-name) 'data))
;;         (list 'car (list 'nthcdr-ex n 'data))))

;; (defun type-case-destructors-macro-1 (case-type rst n)
;;   (cond ((atom rst) nil)
;;         (t (cons (type-destructor-macro case-type
;;                                         (cadar rst)
;;                                         (caar rst)
;;                                         n)
;;                  (type-case-destructors-macro-1 case-type
;;                                                 (cdr rst)
;;                                                 (1+ n))))))

;; ;; Given the type case name and the list of args for the type case, produces a
;; ;; list of destructor definitions for each arg in the type case.
;; (defun type-case-destructors-macro (type-case-name rst-type-case)
;;   (type-case-destructors-macro-1 type-case-name rst-type-case 1))

;; ;; Given a list of type-cases, produces a list of destructor definitions for
;; ;; each argument, for each type case.
;; (defun destructors-macro (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (append (type-case-destructors-macro (caar type-cases)
;;                                                 (cdar type-cases))
;;                    (destructors-macro (cdr type-cases))))))

;; (defun decons-cons-macro (deconstructor-name constructor-name rst-type-case)
;;   (list 'defthm-guarded
;;         (hyphenate-symbols (list deconstructor-name constructor-name))
;;         (list 'implies 
;;               (get-type-constraint rst-type-case)
;;               (list 'equal
;;                     (list deconstructor-name
;;                           (cons constructor-name
;;                                 (get-args rst-type-case)))
;;                     deconstructor-name))))

;; (defun type-case-decons-cons-macro-1 (constructor-name
;;                                       type-case-args rst-type-case-args)
;;   (cond ((atom rst-type-case-args) nil)
;;         (t (cons (decons-cons-macro (cadar rst-type-case-args)
;;                                     constructor-name
;;                                     type-case-args)
;;                  (type-case-decons-cons-macro-1 constructor-name type-case-args
;;                                                 (cdr rst-type-case-args))))))

;; (defun type-case-decons-cons-macro (type-case)
;;   (type-case-decons-cons-macro-1 (car type-case)
;;                                  (cdr type-case)
;;                                  (cdr type-case)))

;; (defun type-decons-cons-macro (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (append (type-case-decons-cons-macro (car type-cases))
;;                    (type-decons-cons-macro (cdr type-cases))))))

;; (defun pair-list-with-atom (lst atm)
;;   (if (atom lst)
;;       nil
;;       (cons (list (car lst) atm) (pair-list-with-atom (cdr lst) atm))))

;; (defun cons-decons-macro (constructor-name rst-type-case)
;;   (list 'defthm-guarded
;;         (if (atom rst-type-case)
;;             (hyphenate-symbols (list constructor-name 'one))
;;             (hyphenate-symbols (cons constructor-name
;;                                      (get-args rst-type-case))))
;;         (list 'implies
;;               (list (add-p-to-name constructor-name) 'data)
;;               (list 'equal
;;                     (cons constructor-name
;;                           (pair-list-with-atom 
;;                            (get-args rst-type-case)
;;                            'data))
;;                     'data))))

;; (defun map-cons-decons-macro (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (cons (cons-decons-macro (caar type-cases) (cdar type-cases))
;;                  (map-cons-decons-macro (cdr type-cases))))))

;; (defun constructor-is-type-macro (type-name constructor-name)
;;   (list 'defthm
;;         (hyphenate-symbols (list constructor-name
;;                                  'is
;;                                  type-name))
;;         (list 'implies 
;;               (list (add-p-to-name constructor-name) 'data)
;;               (list (add-p-to-name type-name) 'data))
;;         ':rule-classes ':tau-system))

;; (defun map-constructor-is-type-macro (type-name type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (cons (constructor-is-type-macro type-name (caar type-cases))
;;                  (map-constructor-is-type-macro type-name (cdr type-cases))))))

;; ;; Destructor-measure-theorems
;; (defun destruct-measure-macro (constructor-name destructor-name)
;;   (list 'defthm
;;         (hyphenate-symbols (list destructor-name 'acl2-count))
;;         (list 'implies
;;               (list (add-p-to-name constructor-name) 'data)
;;               (list '< 
;;                     (list 'acl2-count (list destructor-name 'data))
;;                     (list 'acl2-count 'data)))))

;; (defun type-case-destruct-measure-macro (constructor-name rst-type-case)
;;   (cond ((atom rst-type-case) nil)
;;         (t (cons (destruct-measure-macro constructor-name (cadar rst-type-case))
;;                  (type-case-destruct-measure-macro constructor-name 
;;                                                    (cdr rst-type-case))))))

;; (defun map-type-case-destruct-measure-macro (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (append (type-case-destruct-measure-macro (caar type-cases)
;;                                                      (cdar type-cases))
;;                    (map-type-case-destruct-measure-macro (cdr type-cases))))))

;; ;; One-hot theorems
;; (defun not-all-elim-macro (x)
;;   (cond ((atom x) nil)
;;         (t (cons (list 'not (list (add-p-to-name (car x)) 'data)) 
;;                  (not-all-elim-macro (cdr x))))))

;; (defun type-case-elim-macro (type-name constructor-name
;;                              other-constructor-names)
;;   (list 'defthm-guarded
;;         (hyphenate-symbols (list type-name constructor-name 'elim))
;;         (list 'implies 
;;               (append (list 'and
;;                             (list (add-p-to-name type-name) 'data))
;;                       (not-all-elim-macro other-constructor-names))
;;               (list (add-p-to-name constructor-name) 'data))))

;; (defun map-type-case-elim-macro-1 (type-name rst-constructor-names
;;                                    constructor-names)
;;   (cond ((atom rst-constructor-names) nil)
;;         (t (cons (type-case-elim-macro type-name 
;;                                        (car rst-constructor-names)
;;                                        (remove (car rst-constructor-names)
;;                                                constructor-names))
;;                  (map-type-case-elim-macro-1 type-name
;;                                              (cdr rst-constructor-names)
;;                                              constructor-names)))))

;; (defun map-type-case-elim-macro (type-name constructor-names)
;;   (map-type-case-elim-macro-1 type-name constructor-names constructor-names))

;; (defun cars (l)
;;   (cond ((atom l) nil)
;;         (t (cons (caar l) (cars (cdr l))))))

;; ;; constructorp-constructor

;; (defun constructorp-constructor-macro (constructor-name rst-type-case)
;;   (list 'defthm-guarded 
;;         (hyphenate-symbols (list (add-p-to-name constructor-name) 
;;                                  constructor-name))
;;         (list 'implies
;;               (get-type-constraint rst-type-case)
;;               (list (add-p-to-name constructor-name)
;;                     (cons constructor-name (get-args rst-type-case))))))

;; (defun map-constructorp-constructor-macro (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (cons (constructorp-constructor-macro (caar type-cases)
;;                                                  (cdar type-cases))
;;                  (map-constructorp-constructor-macro (cdr type-cases))))))

;; ;; type cases don't overlap
;; (defun not-constructorp-constructor-macro (not-constructor-name
;;                                            constructor-name rst-type-case)
;;   (list 'defthm-guarded
;;         (hyphenate-symbols (list constructor-name
;;                                  'not 
;;                                  (add-p-to-name not-constructor-name)))
;;         (list 'implies
;;               (get-type-constraint rst-type-case)
;;               (list 'not (list (add-p-to-name not-constructor-name)
;;                                (cons constructor-name (get-args
;;                                                        rst-type-case)))))))

;; (defun map-not-constructorp-constructor-macro (not-constructor-names
;;                                                constructor-name rst-type-case)
;;   (cond ((atom not-constructor-names) nil)
;;         (t (cons (not-constructorp-constructor-macro 
;;                   (car not-constructor-names)
;;                   constructor-name rst-type-case)
;;                  (map-not-constructorp-constructor-macro
;;                   (cdr not-constructor-names)
;;                   constructor-name rst-type-case)))))

;; (defun map-map-not-constructorp-constructor-macro-1 (constructor-names
;;                                                      type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (append (map-not-constructorp-constructor-macro
;;                     (remove (caar type-cases) constructor-names)
;;                     (caar type-cases)
;;                     (cdar type-cases))
;;                    (map-map-not-constructorp-constructor-macro-1
;;                     constructor-names (cdr type-cases))))))

;; (defun map-map-not-constructorp-constructor-macro (type-cases)
;;   (map-map-not-constructorp-constructor-macro-1 (cars type-cases) type-cases))

;; (defun arity-0-uniqueness-macro (constructor-name)
;;   (list 'defthm
;;         (hyphenate-symbols (list constructor-name 'unique))
;;         (list 'implies
;;               (list (add-p-to-name constructor-name) 'data1)
;;               (list 'equal 'data1 (list constructor-name)))
;;         ':rule-classes ':forward-chaining))

;; (defun map-arity-0-uniqueness-macro (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (if (consp (cdar type-cases))
;;                (map-arity-0-uniqueness-macro (cdr type-cases))
;;                (cons (arity-0-uniqueness-macro (caar type-cases))
;;                      (map-arity-0-uniqueness-macro (cdr type-cases)))))))

;; (defun typep-consp (type-name)
;;   (list 'defthm 
;;         (hyphenate-symbols (list (add-p-to-name type-name)
;;                                  'consp))
;;         (list 'implies
;;               (list (add-p-to-name type-name) 'data)
;;               (list 'consp 'data))))

;; (defun get-predicates-1 (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (cons (add-p-to-name (caar type-cases))
;;                  (get-predicates-1 (cdr type-cases))))))

;; (defun get-predicates (type-name type-cases)
;;   (cons (add-p-to-name type-name)
;;         (get-predicates-1 type-cases)))

;; (defun get-constructors (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (cons (caar type-cases) (get-constructors (cdr type-cases))))))

;; (defun get-destructors-type-case (rst-type-case)
;;   (cond ((atom rst-type-case) nil)
;;         (t (cons (cadar rst-type-case) 
;;                  (get-destructors-type-case (cdr rst-type-case))))))

;; (defun get-destructors (type-cases)
;;   (cond ((atom type-cases) nil)
;;         (t (append (get-destructors-type-case (cdar type-cases))
;;                    (get-destructors (cdr type-cases))))))

;; (defmacro defcoproduct-explicit-destructor-names (type &rest type-cases)
;;   (append 
;;    (list 'progn
;;          (list 'defpredicate
;;                (add-p-to-name type)
;;                (list 'data)
;;                (list 'and
;;                      (list 'consp 'data)
;;                      (cons 'or (map-type-case-macro type-cases)))))
;;    (list (typep-consp type))
;;    (map-type-case-def-macro type-cases)
;;    (map-constructor-is-type-macro type type-cases)
;;    (map-construct-type-case-macro type type-cases)
;;    (destructors-macro type-cases)
;;    (type-decons-cons-macro type-cases)
;;    (map-cons-decons-macro type-cases)
;;    (map-type-case-destruct-measure-macro type-cases)
;;    (map-type-case-elim-macro type (cars type-cases))
;;    (map-constructorp-constructor-macro type-cases)
;;    (map-map-not-constructorp-constructor-macro type-cases)
;;    (map-arity-0-uniqueness-macro type-cases) ;; TODO: generalize this
;;    (list (list 'deftheory
;;                (hyphenate-symbols (list type 'types))
;;                (list 'quote (get-predicates type type-cases))))
;;    (list (list 'deftheory
;;                (hyphenate-symbols (list type 'constructors))
;;                (list 'quote (get-constructors type-cases))))
;;    (list (list 'deftheory
;;                (hyphenate-symbols (list type 'destructors))
;;                (list 'quote (get-destructors type-cases))))
;;    (list (list 'in-theory 
;;                (list 'disable (hyphenate-symbols 
;;                                (list type 'types)))))
;;    (list (list 'in-theory 
;;                (list 'disable (hyphenate-symbols 
;;                                (list type 'constructors)))))
;;    (list (list 'in-theory 
;;                (list 'disable (hyphenate-symbols 
;;                                (list type 'destructors)))))))

