(defpackage :HASHTABLE)
(in-package :HASHTABLE)

(defun initialize (test size) 
  (let ((test (car test)))
    (lisp::make-hash-table
     :size size
     :test (cond ((eq test :|EQ|) #'eq)
		 ((eq test :|EQL|) #'eql)
		 ((eq test :|EQUAL|) #'equal)
		 ((eq test :|EQUALP|) #'equalp)
		 (t (error "Unrecognized hash table test: " test))))))
(defun initialize-1 (x) (initialize (car x) (cdr x)))

(defun insert (key item table)
  (setf (gethash key table) item)
  ())
(defun insert-1 (x) (insert (svref x 0) (svref x 1) (svref x 2)))


(defun lookup (key table)
  (multiple-value-bind 
   (item found?) (gethash key table)
   (if found?
       (cons :|Some| item)
     (cons :|None| ()))))
(defun lookup-1 (x) (lookup (car x) (cdr x)))


