;;;Changed from :HASHTABLE for compatibility with cmulisp
(defpackage :HASHTABLE-SPEC)
(in-package :HASHTABLE-SPEC)

(defun initialize-2 (test size) 
  (let ((test (car test)))
    (common-lisp::make-hash-table
     :size size
     :test (cond ((eq test :|EQ|) #'eq)
		 ((eq test :|EQL|) #'eql)
		 ((eq test :|EQUAL|) #'equal)
		 ((eq test :|EQUALP|) #'equalp)
		 (t (error "Unrecognized hash table test: " test))))))
(defun initialize (x) (initialize-2 (car x) (cdr x)))

(defun insert-3 (key item table)
  (setf (gethash key table) item)
  ())
(defun insert (x) (insert-3 (svref x 0) (svref x 1) (svref x 2)))


(defun lookup-2 (key table)
  (multiple-value-bind 
   (item found?) (gethash key table)
   (if found?
       (cons :|Some| item)
     (cons :|None| ()))))
(defun lookup (x) (lookup-2 (car x) (cdr x)))


